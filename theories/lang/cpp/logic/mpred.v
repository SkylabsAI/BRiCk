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

Notation "i '.=' ( L , j )" := (mlens_set L j i) (at level 50, format "i  .=  ( L ,  j )") : stdpp_scope.
Notation "i '.^' L " := (mlens_get L i) (at level 49, format "i .^ L") : stdpp_scope.

Program Definition Lid {I} : MLens I I := {|
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
  mlens_get := fun i => (i.^L).1 ;
  mlens_set := fun j i => i .= (L, (j, (i.^L).2)) ;
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
  rewrite (_: ((i.^L).1, (i.^L).2) = i.^L).
  - by rewrite mlens_set_get.
  - by destruct (mlens_get L i).
Qed.
Next Obligation. intros ??? L ???. rewrite /= mlens_get_set mlens_set_set //. Qed.

Program Definition MLens_right {I J K} (L: MLens I (J *i K)) : MLens I K :=
{|
  mlens_get := fun i => (i.^L).2 ;
  mlens_set := fun k i => i .= (L, ((i.^L).1, k)) ;
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
  rewrite (_: ((i.^L).1, (i.^L).2) = i.^L).
  - by rewrite mlens_set_get.
  - by destruct (mlens_get L i).
Qed.
Next Obligation. intros ??? L ???. rewrite /= mlens_get_set mlens_set_set //. Qed.

(* TODO: is this canonical? *)
(* Lj <= Lk *)
Record mlens_le {I J K : biIndex} (Lj: MLens I J) (Lk: MLens I K) :=
mkMLensLe {
  mlens_le_get i1 i2 : i1.^Lk = i2.^Lk -> i1.^Lj = i2.^Lj ;
  (* set_K (get_K (set_J j i)) i = set_J j i *)
  mlens_le_set_inner i j : i .= (Lk, (i .= (Lj, j)).^Lk) = i .= (Lj, j);
  (* set outer overwrites: set_K k (set_J j i) = set_K k i *)
  mlens_le_set_outer i j k : (i .= (Lj, j)) .= (Lk, k) = i .= (Lk, k);
}.

Section mlens_le.
  Context {I J : biIndex}.

  Lemma mlens_le_reflexive (L: MLens I J): mlens_le L L.
  Proof.
    constructor.
    - done.
    - intros. by rewrite mlens_get_set.
    - intros. by rewrite mlens_set_set.
  Qed.

  Lemma mlens_le_transitive {K H}
    (Lj : MLens I J) (Lk : MLens I K) (Lh : MLens I H) :
    mlens_le Lj Lk -> mlens_le Lk Lh -> mlens_le Lj Lh.
  Proof.
    intros Le1 Le2. constructor.
    - intros. by apply Le1, Le2.
    - intros. by rewrite -(mlens_le_set_inner _ _ Le1) (mlens_le_set_inner _ _ Le2).
    - intros i j h.
      by rewrite -(mlens_le_set_inner _ _ Le1) (mlens_le_set_outer _ _ Le2).
  Qed.

  Lemma mlens_le_Lid (L: MLens I J): mlens_le L Lid.
  Proof.
    constructor.
    - by move => ?? /= ->.
    - done.
    - done.
  Qed.

  Lemma mlens_le_left {K} (L: MLens I (J *i K)) : mlens_le (MLens_left L) L.
  Proof.
    constructor.
    - by move => ?? /= ->.
    - intros. by rewrite mlens_get_set.
    - intros. by rewrite mlens_set_set.
  Qed.

  Lemma mlens_le_right {K} (L: MLens I (J *i K)) : mlens_le (MLens_right L) L.
  Proof.
    constructor.
    - by move => ?? /= ->.
    - intros. by rewrite mlens_get_set.
    - intros. by rewrite mlens_set_set.
  Qed.
End mlens_le.

Section Bi.
Context {I J : biIndex} {PROP : bi}.
Notation monPred := (monPred I PROP).
Implicit Type (P Q : monPred).

(* @(ml,j) P *)
Program Definition monPred_exactly_with (L : MLens I J) (j : J) P :=
  MonPred (λ i, P (i .= (L, j)))%I _.
Next Obligation. intros ?? P ???. rewrite mlens_set_mono; eauto. Qed.

(* <obj>_{ml} P *)
Definition monPred_objectively_with (L : MLens I J) P : monPred :=
  Forall j : J, monPred_exactly_with L j P.

Program Definition monPred_embed
  (L : MLens I J) (P : monpred.monPred J PROP) : monPred :=
  MonPred (λ i, P (i.^L))%I _.
Next Obligation. intros ? P ???. rewrite mlens_get_mono; eauto. Qed.

Definition monPred_atleast (L : MLens I J) (j : J) : monPred :=
  monPred_embed L (monPred_in j).

End Bi.

(* TODO: ml should be TC-searched using the type I and J *)
(* @j P <obj>_J P *)
Notation "'@(' L , j ')' P" := (monPred_exactly_with L j P)
  (at level 50, format "@( L , j )  P") : bi_scope.
Notation "'<obj>_{' L '}' P" := (monPred_objectively_with L P)
  (at level 49, format "<obj>_{ L }  P"): bi_scope.

(* ObjectiveWith respect to J *)
Class ObjectiveWith {I J: biIndex} {PROP: bi} (L: MLens I J) (P: monPred I PROP) :=
  objective_with i j : P i -∗ P (i .= (L, j)).
Arguments ObjectiveWith {_ _ _} _ _%I.
Arguments objective_with {_ _ _} _ _%I {_}.
Hint Mode ObjectiveWith ! ! + + ! : typeclass_instances.
Instance: Params (@ObjectiveWith) 3 := {}.

Section BiProperties.
Context {I J : biIndex} {PROP : bi}.
Notation monPred := (monPred I PROP).
Implicit Type (P Q : monPred).

Global Instance monPred_exactly_with_mono (L : MLens I J) :
  Proper (sqsubseteq ==> bi_entails ==> bi_entails)
         (@monPred_exactly_with _ _ PROP L).
Proof.
  intros i1 i2 Lei P Q EN. constructor => i /=.
  rewrite EN mlens_set_mono; eauto.
Qed.
Global Instance monPred_exactly_with_proper (L : MLens I J) j :
  Proper ((≡) ==> (≡)) (@monPred_exactly_with _ _ PROP L j).
Proof.
  intros P Q EQ.
  iSplit; iIntros "P";
    iApply (monPred_exactly_with_mono with "P"); eauto; by rewrite EQ.
Qed.

Global Instance monPred_objectively_with_mono (L : MLens I J) :
  Proper (bi_entails ==> bi_entails)
         (@monPred_objectively_with _ _ PROP L).
Proof.
  intros P Q EN. constructor => i /=. rewrite !monPred_at_forall /=.
  by setoid_rewrite EN.
Qed.
Global Instance monPred_objectively_with_proper (L : MLens I J) :
  Proper ((≡) ==> (≡)) (@monPred_objectively_with _ _ PROP L).
Proof.
  intros P Q EQ.
  iSplit; iIntros "P";
    iApply (monPred_objectively_with_mono with "P"); eauto; by rewrite EQ.
Qed.

Lemma monPred_objectively_with_lens_mono {K} (Lj : MLens I J) (Lk : MLens I K) P :
  mlens_le Lj Lk ->
  <obj>_{Lk} P |-- <obj>_{Lj} P.
Proof.
  intros Le. constructor => i /=. rewrite !monPred_at_forall /=.
  iIntros "P" (x).
  iSpecialize ("P" $! (i .= (Lj, x)).^Lk). by rewrite mlens_le_set_inner.
Qed.

(* Lemma monPred_objectively_commute
  <obj>_{ml1} <obj>_{ml2} P -|- <obj>_{ml2} <obj>_{ml1} P *)

Lemma monPred_objectively_with_exactly_with_idemp (L : MLens I J) (j : J) P :
  @(L,j) <obj>_{L} P -|- <obj>_{L} P.
Proof.
  constructor => i /=. rewrite !monPred_at_forall /=.
  setoid_rewrite mlens_set_set. eauto.
Qed.

Lemma monPred_objectively_with_exactly_with_commute (L : MLens I J) (j : J) P :
  <obj>_{L} P |-- @(L,j) P.
Proof. constructor => i /=. rewrite monPred_at_forall /=. eauto. Qed.

Lemma monPred_objectively_with_elim (L : MLens I J) P :
  <obj>_{L} P |-- P.
Proof.
  constructor => i /=. rewrite monPred_at_forall /=.
  rewrite -{2}(mlens_set_get L i). eauto.
Qed.

Lemma monPred_objectively_with_exactly_with (L : MLens I J) (j : J) P :
  @(L,j) <obj>_{L} P |-- @(L,j) P.
Proof.
  constructor => i /=. rewrite monPred_at_forall /=.
  setoid_rewrite mlens_set_set. eauto.
Qed.

Global Instance monPred_objectively_with_objective_with_mono {K}
  (Lj : MLens I J) (Lk : MLens I K) P :
  mlens_le Lj Lk ->
  ObjectiveWith Lj (<obj>_{Lk} P).
Proof.
  intros Le i j. rewrite !monPred_at_forall /=.
  by setoid_rewrite mlens_le_set_outer.
Qed.

Global Instance monPred_objectively_with_objective_with (L : MLens I J) P :
  ObjectiveWith L (<obj>_{L} P).
Proof.
  apply monPred_objectively_with_objective_with_mono, mlens_le_reflexive.
Qed.

Global Instance monPred_exactly_with_objective_with_mono {K}
  (Lj : MLens I J) (Lk : MLens I K) P k :
  mlens_le Lj Lk ->
  ObjectiveWith Lj (@(Lk,k) P).
Proof. intros Le i j. by rewrite /= mlens_le_set_outer. Qed.

Global Instance monPred_exactly_with_objective_with (Lj : MLens I J) P j :
  ObjectiveWith Lj (@(Lj,j) P).
Proof. apply monPred_exactly_with_objective_with_mono, mlens_le_reflexive. Qed.

Lemma monPred_objectively_with_id_objectively P :
  <obj> P -|- <obj>_{Lid} P.
Proof.
  constructor => i /=. by rewrite monPred_at_forall monPred_at_objectively /=.
Qed.
End BiProperties.
