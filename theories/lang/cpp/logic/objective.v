(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

From iris.bi Require Import bi monpred.
From iris.base_logic.lib Require Import
      fancy_updates invariants cancelable_invariants own.
From iris.proofmode Require Import tactics.

From bedrock.lang.cpp.logic Require Import pred.

Set Default Proof Using "Type".
Set Suggest Proof Using.

(* the details of what a component is, and how it is to be defined, is still
  to be decided *)
Structure component (I : biIndex) := Component {
  component_type :> Type;
  component_proj : I -> component_type;
  (* component_upd : I -> component_type -> I;
  component_rel : SqSubsetEq component_type;
  component_rel_preorder: PreOrder (⊑@{component_type}) ;
  component_proj_rel_proper: Proper ((⊑) ==> (⊑)) component_proj *)
}.

Arguments component_proj {_} _.
(* Arguments component_upd {_} _ _. *)


(* [i] and [j] are the same for all components in [coms] *)
Definition eq_with {I} (coms: list (component I)) (i j : I) : Prop :=
  List.Forall (λ c, component_proj c i = component_proj c j) coms.

Instance eq_with_equivalence {I} (coms: list (component I))
  : Equivalence (eq_with coms).
Proof.
  constructor.
  - intros i. by apply Forall_true.
  - intros i j. rewrite /eq_with !Forall_forall.
    intros EQ x Inx. by rewrite (EQ _ Inx).
  - intros i j k. rewrite /eq_with !Forall_forall.
    intros EQ1 EQ2 x Inx. by rewrite (EQ1 _ Inx) (EQ2 _ Inx).
Qed.

Instance eq_with_mono {I} :
  Proper ((⊆) ==> (=) ==> (=) ==> flip (impl)) (@eq_with I).
Proof.
  intros coms coms' SUB i ? <- j ? <-. rewrite /eq_with !Forall_forall.
  intros EQ x Inx. by apply EQ, SUB.
Qed.

(* ObjectiveBut for all but those in [coms], that is, [P] holds true for
  arbitrary thread_info’s that only agree on coms *)
Class ObjectiveBut {I: biIndex} {PROP: bi}
  (coms: list (component I)) (P: monPred I PROP) :=
  objective_at_but i j : eq_with coms i j -> P i -∗ P j.
Arguments ObjectiveBut {_ _} _ _%I.
Arguments objective_at_but {_ _} _ _%I {_}.
Hint Mode ObjectiveBut + + ! ! : typeclass_instances.
Instance: Params (@ObjectiveBut) 2 := {}.

Section Bi.
Context {I : biIndex} {PROP : bi}.
Implicit Types i : I.
Notation monPred := (monPred I PROP).
Notation component := (component I).
Implicit Types P Q : monPred.

(* explicitly monotonizing with monPred_upclosed *)
Definition monPred_objectively_but_def (coms : list component) P : monPred :=
  monPred_upclosed (λ j, ∀ i, ⌜eq_with coms i j⌝ → P i)%I.
Definition monPred_objectively_but_aux : seal (@monPred_objectively_but_def).
Proof. by eexists. Qed.
Definition monPred_objectively_but := monPred_objectively_but_aux.(unseal).
Definition monPred_objectively_but_eq : @monPred_objectively_but = _ := monPred_objectively_but_aux.(seal_eq).

End Bi.

Arguments monPred_objectively_but {_ _} _ _%I.
Notation "'<obj>{-' c '}' P" := (monPred_objectively_but c P) (at level 50) : bi_scope.

Section properties.
Context {I : biIndex} {PROP : bi}.
Local Notation monPred := (monPred I PROP).
Implicit Types i : I.
Implicit Types P Q : monPred.

Lemma monPred_objectively_but_mono' :
  Proper ((⊆) ==> (≡) ==> (bi_entails)) (@monPred_objectively_but I PROP).
Proof.
  intros coms coms' SUB P1 P2 EQ2. constructor => i.
  rewrite monPred_objectively_but_eq /=.
  iIntros "P" (j Lej i' EQ); iSpecialize ("P" $! j with "[%//]").
  rewrite -EQ2. iApply ("P" with "[%]"). by rewrite ->SUB.
Qed.

Global Instance monPred_objectively_but_proper :
  Proper ((=) ==> (≡) ==> (≡)) (@monPred_objectively_but I PROP).
Proof.
  intros coms coms' <- P P' EQ.
  iSplit; iIntros "P".
  - iApply monPred_objectively_but_mono'; eauto.
  - iApply monPred_objectively_but_mono'. eauto. rewrite EQ; eauto. done.
Qed.

Lemma monPred_objectively_but_mono coms coms' P :
  coms ⊆ coms' -> <obj>{- coms} P |-- <obj>{- coms'} P.
Proof. intros SUB. by apply monPred_objectively_but_mono'. Qed.

Lemma monPred_objectively_but_nil P :
  <obj>{- nil} P -|- <obj> P.
Proof.
  rewrite monPred_objectively_unfold monPred_objectively_but_eq.
  constructor => i.
  rewrite /= monPred_at_embed.
  iSplit; iIntros "P".
  - iIntros (i'). iSpecialize ("P" $! i with "[%//]").
    iApply ("P" with "[%]"). by constructor.
  - iIntros (j Lej i' _). by iApply "P".
Qed.

Lemma monPred_objectively_but_objective_but coms P `{!ObjectiveBut coms P} :
  <obj>{- coms} P -|- P.
Proof.
  rewrite monPred_objectively_but_eq. constructor. intros i.
  rewrite /=.
  iSplit; iIntros "P".
  - iSpecialize ("P" $! i with "[%//]"). by iApply ("P" $! i with "[%]").
  - iIntros (j Lej i' EQ). rewrite Lej.
    iApply (objective_at_but with "P"); eauto.
    by symmetry.
Qed.

Instance monPred_objectively_but_objective_but_instance coms P :
  ObjectiveBut coms (<obj>{- coms} P).
Proof.
  intros i j EQ. rewrite monPred_objectively_but_eq /=.
  iIntros "P" (j' Lej i' Lei').
Abort.

End properties.
