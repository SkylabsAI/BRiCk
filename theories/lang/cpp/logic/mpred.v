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

Structure MLens {I J : biIndex} : Type := MLensMake {
  mlens_get : I -> J ;
  mlens_set : J -> I -> I ;
  mlens_get_mono : Proper (sqsubseteq ==> sqsubseteq) mlens_get ;
  mlens_set_mono : Proper (sqsubseteq ==> sqsubseteq ==> sqsubseteq) mlens_set ;
  mlens_get_set : forall i j, mlens_get (mlens_set j i) = j ;
  mlens_set_get : forall i, mlens_set (mlens_get i) i = i ;
  mlens_set_set : forall i j1 j2, mlens_set j1 (mlens_set j2 i) = mlens_set j1 i ;
}.

Arguments MLens : clear implicits.

Program Definition MLens_id {I} : MLens I I := {|
  mlens_get := fun i => i;
  mlens_set := fun j i => j;
|}.
Next Obligation. by intros ??? L ???. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Program Definition biIndex_prod (I J : biIndex) : biIndex := {|
  bi_index_type := I * J ;
  bi_index_rel  := prod_relation (⊑) (⊑);
|}.
Next Obligation.
  intros. constructor.
  - done.
  - apply prod_relation_trans; apply _.
Qed.

Infix "*i" := biIndex_prod (at level 120, right associativity): stdpp_scope.

Program Definition MLens_left {I J K} (L: MLens I (J *i K)) : MLens I J :=
{|
  mlens_get := fun i => (mlens_get L i).1 ;
  mlens_set := fun j i => mlens_set L (j, (mlens_get L i).2) i ;
|}.
Next Obligation. intros ??? L ???. by rewrite mlens_get_mono; eauto. Qed.
Next Obligation.
  intros ??? L ??? ???. rewrite mlens_set_mono; eauto.
  split; [done|simpl].
  rewrite mlens_get_mono; eauto.
Qed.
Next Obligation. intros ??? L ??. by rewrite /= mlens_get_set. Qed.
Next Obligation.
  simpl. intros ??? L i.
  rewrite (_: ((mlens_get L i).1, (mlens_get L i).2) = mlens_get L i).
  - by rewrite mlens_set_get.
  - by destruct (mlens_get L i).
Qed.
Next Obligation. intros ??? L ???. rewrite /= mlens_get_set mlens_set_set //. Qed.

Program Definition MLens_right {I J K} (L: MLens I (J *i K)) : MLens I K :=
{|
  mlens_get := fun i => (mlens_get L i).2 ;
  mlens_set := fun k i => mlens_set L ((mlens_get L i).1, k) i ;
|}.
Next Obligation. intros ??? L ???. by rewrite mlens_get_mono; eauto. Qed.
Next Obligation.
  intros ??? L ??? ???. rewrite mlens_set_mono; eauto.
  split; [simpl|done].
  rewrite mlens_get_mono; eauto.
Qed.
Next Obligation. intros ??? L ??. by rewrite /= mlens_get_set. Qed.
Next Obligation.
  simpl. intros ??? L i.
  rewrite (_: ((mlens_get L i).1, (mlens_get L i).2) = mlens_get L i).
  - by rewrite mlens_set_get.
  - by destruct (mlens_get L i).
Qed.
Next Obligation. intros ??? L ???. rewrite /= mlens_get_set mlens_set_set //. Qed.

Section Bi.
Context {I : biIndex} {PROP : bi}.
Notation monPred := (monPred I PROP).
Implicit Type (P Q : monPred).

(* @(ml,j) P *)
Program Definition monPred_exactly_with {J} (ml : MLens I J) (j : J) P :=
  MonPred (λ i, P (mlens_set ml j i))%I _.
Next Obligation. intros ??? P ???. rewrite mlens_set_mono; eauto. Qed.

(* <obj>_{ml} P *)
Definition monPred_objectively_with {J} (ml : MLens I J) P : monPred :=
  Forall j : J, monPred_exactly_with ml j P.

Program Definition monPred_embed {J}
  (ml : MLens I J) (P : monpred.monPred J PROP) : monPred :=
  MonPred (λ i, P (mlens_get ml i))%I _.
Next Obligation. intros ?? P ???. rewrite mlens_get_mono; eauto. Qed.

Definition monPred_atleast {J} (ml : MLens I J) (j : J) : monPred :=
  monPred_embed ml (monPred_in j).

End Bi.

(* TODO: ml should be TC-searched using the type I and J *)
(* @j P <obj>_J P *)
Notation "'@(' ml , j ')' P" := (monPred_exactly_with ml j P)
  (at level 50, format "@( ml , j )  P") : bi_scope.
Notation "'<obj>_{' ml '}' P" := (monPred_objectively_with ml P)
  (at level 49, format "<obj>_{ ml }  P"): bi_scope.

(* ObjectiveWith respect to J *)
Class ObjectiveWith {I J: biIndex} {PROP: bi} (L: MLens I J) (P: monPred I PROP) :=
  objective_with i j : P i -∗ P (mlens_set L j i).
Arguments ObjectiveWith {_ _ _} _ _%I.
Arguments objective_with {_ _ _} _ _%I {_}.
Hint Mode ObjectiveWith ! ! + + ! : typeclass_instances.
Instance: Params (@ObjectiveWith) 3 := {}.

Section BiProperties.
Context {I : biIndex} {PROP : bi}.
Notation monPred := (monPred I PROP).
Implicit Type (P Q : monPred).

(* TODO: Lens mono *)
Global Instance monPred_exactly_with_mono {J} (L : MLens I J) :
  Proper (sqsubseteq ==> bi_entails ==> bi_entails)
         (@monPred_exactly_with _ PROP _ L).
Proof.
  intros i1 i2 Lei P Q EN. constructor => i /=.
  rewrite EN mlens_set_mono; eauto.
Qed.
(* TODO: Lens equiv *)
Global Instance monPred_exactly_with_proper {J} (L : MLens I J) j :
  Proper ((≡) ==> (≡)) (@monPred_exactly_with _ PROP _ L j).
Proof.
  intros P Q EQ.
  iSplit; iIntros "P";
    iApply (monPred_exactly_with_mono with "P"); eauto; by rewrite EQ.
Qed.

(* TODO Lens mono *)
Global Instance monPred_objectively_with_mono {J} (L : MLens I J) :
  Proper (bi_entails ==> bi_entails)
         (@monPred_objectively_with _ PROP _ L).
Proof.
  intros P Q EN. constructor => i /=. rewrite !monPred_at_forall /=.
  by setoid_rewrite EN.
Qed.
Global Instance monPred_objectively_with_proper {J} (L : MLens I J) :
  Proper ((≡) ==> (≡)) (@monPred_objectively_with _ PROP _ L).
Proof.
  intros P Q EQ.
  iSplit; iIntros "P";
    iApply (monPred_objectively_with_mono with "P"); eauto; by rewrite EQ.
Qed.

(* Lemma monPred_objectively_commute
  <obj>_{ml1} <obj>_{ml2} P -|- <obj>_{ml2} <obj>_{ml1} P

Lemma monPred_objectively_with {J K} (ml1 : MLens I J) (ml2 : MLens I K) P (K <= J) :
  <obj>_{ml1} P |-- <obj>_{ml2} P. *)

Lemma monPred_objectively_with_exactly_with_idemp {J} (ml : MLens I J) (j : J) P :
  @(ml,j) <obj>_{ml} P -|- <obj>_{ml} P.
Proof.
  constructor => i /=. rewrite !monPred_at_forall /=.
  setoid_rewrite mlens_set_set. eauto.
Qed.

Lemma monPred_objectively_with_exactly_with_commute {J} (ml : MLens I J) (j : J) P :
  <obj>_{ml} P |-- @(ml,j) P.
Proof. constructor => i /=. rewrite monPred_at_forall /=. eauto. Qed.

Lemma monPred_objectively_with_elim {J} (ml : MLens I J) P :
  <obj>_{ml} P |-- P.
Proof.
  constructor => i /=. rewrite monPred_at_forall /=.
  rewrite -{2}(mlens_set_get ml i). eauto.
Qed.

Lemma monPred_objectively_with_exactly_with {J} (ml : MLens I J) (j : J) P :
  @(ml,j) <obj>_{ml} P |-- @(ml,j) P.
Proof.
  constructor => i /=. rewrite monPred_at_forall /=.
  setoid_rewrite mlens_set_set. eauto.
Qed.

(* L <= L' -> ObjectiveWith L (<obj>_{L'} P) *)
Global Instance monPred_objectively_with_objective_with {J} (L : MLens I J) P :
  ObjectiveWith L (<obj>_{L} P).
Proof.
  intros i j. rewrite !monPred_at_forall /=.
  iIntros "P" (j'). rewrite mlens_set_set. eauto.
Qed.
End BiProperties.
