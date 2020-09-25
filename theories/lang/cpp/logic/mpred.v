(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.bi Require Import bi monpred.
From iris.proofmode Require Import tactics.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Implicit Types (I J K : biIndex) (PROP : bi).

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

(* TODO: is this canonical? *)
(* Lj <= Lk *)
Record mlens_le {I J K} (Lj: MLens I J) (Lk: MLens I K) :=
mkMLensLe {
  mlens_le_get i1 i2 : i1.^Lk = i2.^Lk -> i1.^Lj = i2.^Lj ;
  (* set_K (get_K (set_J j i)) i = set_J j i *)
  mlens_le_set_inner i j : i .= (Lk, (i .= (Lj, j)).^Lk) = i .= (Lj, j);
  (* set outer overwrites: set_K k (set_J j i) = set_K k i *)
  mlens_le_set_outer i j k : (i .= (Lj, j)) .= (Lk, k) = i .= (Lk, k);
}.

Definition mlens_equiv {I J K} (Lj: MLens I J) (Lk: MLens I K) :=
  mlens_le Lj Lk /\ mlens_le Lk Lj.

Definition mlens_disjoint {I J K} (Lj: MLens I J) (Lk: MLens I K) :=
  forall i j k, (i .= (Lj, j)) .= (Lk, k) = (i .= (Lk, k)) .= (Lj, j).

Infix ".<=" := mlens_le (at level 90) : stdpp_scope.
Infix ".≡"  := mlens_equiv (at level 90) : stdpp_scope.
Infix ".##" := mlens_disjoint (at level 90) : stdpp_scope.


Lemma mlens_le_reflexive {I J} (L: MLens I J): L .<= L.
Proof.
  constructor.
  - done.
  - intros. by rewrite mlens_get_set.
  - intros. by rewrite mlens_set_set.
Qed.

Lemma mlens_le_transitive {I J K H}
  (Lj : MLens I J) (Lk : MLens I K) (Lh : MLens I H) :
  Lj .<= Lk -> Lk .<= Lh -> Lj .<= Lh.
Proof.
  intros Le1 Le2. constructor.
  - intros. by apply Le1, Le2.
  - intros. by rewrite -(mlens_le_set_inner _ _ Le1) (mlens_le_set_inner _ _ Le2).
  - intros i j h.
    by rewrite -(mlens_le_set_inner _ _ Le1) (mlens_le_set_outer _ _ Le2).
Qed.

Lemma mlens_equiv_reflexive {I J} (L: MLens I J): mlens_equiv L L.
Proof. split; apply mlens_le_reflexive. Qed.

Lemma mlens_equiv_symmetric {I J K} (Lj : MLens I J) (Lk : MLens I K) :
  mlens_equiv Lj Lk <-> mlens_equiv Lk Lj.
Proof. rewrite /mlens_equiv. intuition. Qed.

Lemma mlens_equiv_transitive {I J K H}
  (Lj : MLens I J) (Lk : MLens I K) (Lh : MLens I H) :
  mlens_equiv Lj Lk -> mlens_equiv Lk Lh -> mlens_equiv Lj Lh.
Proof. intros [Le1 Le2] [Le3 Le4]. split; eapply mlens_le_transitive; eauto. Qed.

Lemma mlens_disjoint_symmetric {I J K} (Lj: MLens I J) (Lk: MLens I K) :
  Lj .## Lk <-> Lk .## Lj.
Proof. split; intros DISJ ???; by rewrite DISJ. Qed.

Lemma mlens_disjoint_get_set {I J K} (Lj: MLens I J) (Lk: MLens I K)
  (DISJ: Lj .## Lk ) :
  forall i j, (i .= (Lj, j)).^Lk = i.^Lk.
Proof.
  intros i j. by rewrite -{1}(mlens_set_get Lk i) -DISJ mlens_get_set.
Qed.


Section Bi.
  Context {I J : biIndex} {PROP : bi}.
  Notation monPred := (monPred I PROP).
  Implicit Type (P Q : monPred).

  (* @(ml,j) P *)
  Program Definition monPred_exactly_at (L : MLens I J) (j : J) P :=
    MonPred (λ i, P (i .= (L, j)))%I _.
  Next Obligation. intros ?? P ???. rewrite mlens_set_mono; eauto. Qed.

  (* <obj>_{ml} P *)
  Definition monPred_objectively_with (L : MLens I J) P : monPred :=
    (∀ j : J, monPred_exactly_at L j P)%I.

  Program Definition monPred_embed
    (L : MLens I J) (P : monpred.monPred J PROP) : monPred :=
    MonPred (λ i, P (i.^L))%I _.
  Next Obligation. intros ? P ???. rewrite mlens_get_mono; eauto. Qed.

  Definition monPred_atleast (L : MLens I J) (j : J) : monPred :=
    monPred_embed L (monPred_in j).
End Bi.

(* TODO: ml should be TC-searched using the type I and J *)
(** @j P
    <obj>_J P *)
Notation "'@(' L , j ')' P" := (monPred_exactly_at L j P)
  (at level 50, format "@( L , j )  P") : bi_scope.
Notation "'<obj>_{' L '}' P" := (monPred_objectively_with L P)
  (at level 49, format "<obj>_{ L }  P"): bi_scope.

(* ObjectiveWith respect to J *)
Class ObjectiveWith {I J} {PROP: bi} (L: MLens I J) (P: monPred I PROP) :=
  objective_with i j : P i -∗ P (i .= (L, j)).
Arguments ObjectiveWith {_ _ _} _ _%I.
Arguments objective_with {_ _ _} _ _%I {_}.
Hint Mode ObjectiveWith ! ! + + ! : typeclass_instances.
Instance: Params (@ObjectiveWith) 3 := {}.


Program Definition Lid {I} : MLens I I := {|
  mlens_get := fun i => i;
  mlens_set := fun j i => j;
|}.
Next Obligation. by intros ??? L ???. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Section Lid_properties.
  Context {I}.

  Lemma mlens_le_Lid {J} (L: MLens I J): L .<= Lid.
  Proof. constructor; try done. by move => ?? /= ->. Qed.

  Lemma monPred_objectively_with_id_objectively {PROP} (P: monPred I PROP) :
    <obj> P ⊣⊢ <obj>_{Lid} P.
  Proof.
    constructor => i /=. by rewrite monPred_at_forall monPred_at_objectively /=.
  Qed.

  Lemma monPred_objective_with_id_objective {PROP} (P: monPred I PROP) :
    Objective P <-> ObjectiveWith Lid P.
  Proof. done. Qed.
End Lid_properties.


(** ObjectiveWith *)
Instance monPred_objective_with_lens_mono {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP) :
  Lj .<= Lk ->
  ObjectiveWith Lk P ->
  ObjectiveWith Lj P.
Proof.
  intros Le OW i. iIntros (j') "P".
  rewrite -(mlens_le_set_inner _ Lk) //. by iApply OW.
Qed.

Lemma monPred_objective_with_lens_equiv {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP) :
  mlens_equiv Lj Lk ->
  ObjectiveWith Lj P <-> ObjectiveWith Lk P.
Proof. intros []. split; by apply monPred_objective_with_lens_mono. Qed.


(** objectively_with *)
Section objectivelyWith.
  Context {I J : biIndex} {PROP : bi}.
  Notation monPred := (monPred I PROP).
  Implicit Type (P Q : monPred).

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

  Lemma monPred_objectively_with_elim (L : MLens I J) P :
    <obj>_{L} P ⊢ P.
  Proof.
    constructor => i /=. rewrite monPred_at_forall /=.
    rewrite -{2}(mlens_set_get L i). eauto.
  Qed.

  Lemma monPred_objective_with_intro_objectively_with (L : MLens I J) P :
    ObjectiveWith L P -> P ⊢ <obj>_{L} P.
  Proof.
    intros OBJ. constructor => i /=. rewrite monPred_at_forall /=.
    iIntros "P" (j). by iApply OBJ.
  Qed.

  (* Lemma monPred_objectively_commute
    <obj>_{ml1} <obj>_{ml2} P ⊣⊢ <obj>_{ml2} <obj>_{ml1} P *)

  Lemma monPred_objectively_with_lens_mono {K}
    (Lj : MLens I J) (Lk : MLens I K) P :
    Lj .<= Lk ->
    <obj>_{Lk} P ⊢ <obj>_{Lj} P.
  Proof.
    intros Le. constructor => i /=. rewrite !monPred_at_forall /=.
    iIntros "P" (x).
    iSpecialize ("P" $! (i .= (Lj, x)).^Lk). by rewrite mlens_le_set_inner.
  Qed.

  Global Instance monPred_objectively_with_objective_with (L : MLens I J) P :
    ObjectiveWith L (<obj>_{L} P).
  Proof.
    intros i j. rewrite !monPred_at_forall /=.
    by setoid_rewrite mlens_set_set.
  Qed.
End objectivelyWith.

Lemma monPred_objectively_with_lens_equiv {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP) :
  Lj .≡ Lk ->
  <obj>_{Lj} P ⊣⊢ <obj>_{Lk} P.
Proof.
  intros []. apply bi.equiv_spec.
  split; by apply monPred_objectively_with_lens_mono.
Qed.

Corollary monPred_objectively_with_objective_with_lens_mono {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P: monPred I PROP) :
  Lj .<= Lk ->
  ObjectiveWith Lj (<obj>_{Lk} P).
Proof.
  intros.
  eapply monPred_objective_with_lens_mono; eauto.
  by apply monPred_objectively_with_objective_with.
Qed.

Corollary monPred_objective_with_intro_objectively_with_lens_mono  {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P: monPred I PROP) :
  Lj .<= Lk ->
  ObjectiveWith Lk P ->
  P ⊢ <obj>_{Lj} P.
Proof.
  iIntros (Le OBJ). apply monPred_objective_with_intro_objectively_with.
  eapply monPred_objective_with_lens_mono; eauto.
Qed.


Section exactlyAt.
  Context {I J} {PROP}.
  Implicit Types (P Q: monPred I PROP).
  (* exactly at *)
  Global Instance monPred_exactly_at_mono (L : MLens I J) :
    Proper (sqsubseteq ==> bi_entails ==> bi_entails)
          (@monPred_exactly_at _ _ PROP L).
  Proof.
    intros i1 i2 Lei P Q EN. constructor => i /=.
    rewrite EN mlens_set_mono; eauto.
  Qed.
  Global Instance monPred_exactly_at_proper (L : MLens I J) j :
    Proper ((≡) ==> (≡)) (@monPred_exactly_at _ _ PROP L j).
  Proof.
    intros P Q EQ.
    iSplit; iIntros "P";
      iApply (monPred_exactly_at_mono with "P"); eauto; by rewrite EQ.
  Qed.

  Lemma monPred_exactly_at_elim_objectively_with (L : MLens I J) (j : J) P :
    @(L,j) <obj>_{L} P ⊣⊢ <obj>_{L} P.
  Proof.
    constructor => i /=. rewrite !monPred_at_forall /=.
    setoid_rewrite mlens_set_set. eauto.
  Qed.

  Lemma monPred_objectively_with_into_exactly_at (L : MLens I J) (j : J) P :
    <obj>_{L} P ⊢ @(L,j) P.
  Proof. constructor => i /=. rewrite monPred_at_forall /=. eauto. Qed.

  Corollary monPred_exactly_at_objectively_with_elim (L : MLens I J) (j : J) P :
    @(L,j) <obj>_{L} P ⊢ @(L,j) P.
  Proof.
    etrans; last apply monPred_objectively_with_into_exactly_at.
    by rewrite monPred_exactly_at_elim_objectively_with.
  Qed.

  Global Instance monPred_exactly_at_objective_with (L : MLens I J) P j :
    ObjectiveWith L (@(L,j) P).
  Proof. intros i j'. by rewrite /= mlens_set_set. Qed.
End exactlyAt.

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

Notation "L '.l'" := (MLens_left L)
  (at level 61, left associativity, format "L .l"): stdpp_scope.
Notation "L '.r'" := (MLens_right L)
  (at level 61, left associativity, format "L .r"): stdpp_scope.


Program Definition MLens_join {I J K}
  (Lj: MLens I J) (Lk: MLens I K) (DISJ: mlens_disjoint Lj Lk)
  : MLens I (J *i K) := {|
    mlens_get := fun i => (i.^Lj, i.^Lk);
    mlens_set := fun jk i => (i .= (Lj, jk.1)) .= (Lk, jk.2);
  |}.
Next Obligation. intros ??? ?? ?. split; simpl; by apply mlens_get_mono. Qed.
Next Obligation. intros ??? ??? [] [] [] ???. do 2 (apply mlens_set_mono; auto). Qed.
Next Obligation.
  intros ??? ??? ? []. by rewrite /= mlens_get_set DISJ mlens_get_set. Qed.
Next Obligation. intros ??? ??? ?. by rewrite /= !mlens_set_get. Qed.
Next Obligation.
  intros ??? ???? [][]. by rewrite /= DISJ mlens_set_set DISJ mlens_set_set DISJ. Qed.

Notation "Lj '.+_{' D '}' Lk" := (MLens_join Lj Lk D)
  (at level 65, format "Lj  .+_{ D }  Lk"): stdpp_scope.

Section mlens_prod.
  Context {I J K: biIndex}.
  Implicit Types (L : MLens I (J *i K)).

  Lemma mlens_le_left L : L.l .<= L.
  Proof.
    constructor.
    - by move => ?? /= ->.
    - intros. by rewrite mlens_get_set.
    - intros. by rewrite mlens_set_set.
  Qed.

  Lemma mlens_le_right L : L.r .<= L.
  Proof.
    constructor.
    - by move => ?? /= ->.
    - intros. by rewrite mlens_get_set.
    - intros. by rewrite mlens_set_set.
  Qed.

  Lemma mlens_disjoint_prod L : L.l .## L.r.
  Proof.
    rewrite /mlens_disjoint. intros.
    by rewrite /= !mlens_get_set /= !mlens_set_set.
  Qed.

  Lemma mlens_equiv_split_join L :
    L .≡ L.l .+_{mlens_disjoint_prod L} L.r.
  Proof.
    split; constructor; simpl.
    - intros. by destruct (i1.^L), (i2.^L).
    - intros i [j k]. by rewrite /= !mlens_get_set !mlens_set_set.
    - intros i [j1 k1] [j2 k2]. by rewrite /= !mlens_get_set !mlens_set_set.
    - intros. by destruct (i1.^L), (i2.^L).
    - intros i [j k]. by rewrite /= !mlens_get_set !mlens_set_set.
    - intros i [j1 k1] [j2 k2]. by rewrite /= !mlens_get_set !mlens_set_set.
  Qed.

  Lemma monPred_exactly_at_objective_with_disjoint_left
    {PROP: bi} (Lj : MLens I J) (Lk : MLens I K)
    (D: Lj .## Lk) (P : monPred I PROP) j :
    ObjectiveWith Lk P ->
    ObjectiveWith (Lj .+_{D} Lk) (@(Lj, j) P).
  Proof.
    intros OBJ jk1 jk2. rewrite /= D mlens_set_set -D. apply OBJ.
  Qed.

  Lemma monPred_exactly_at_objective_with_disjoint_right
    {PROP: bi} (Lj : MLens I J) (Lk : MLens I K)
    (D: Lk .## Lj) (P : monPred I PROP) j :
    ObjectiveWith Lk P ->
    ObjectiveWith (Lk .+_{D} Lj) (@(Lj, j) P).
  Proof.
    intros OBJ jk1 jk2. rewrite /= mlens_set_set D. apply OBJ.
  Qed.

  Lemma monPred_objectively_with_objective_with_disjoint_left
    {PROP: bi} (Lj : MLens I J) (Lk : MLens I K)
    (D: Lj .## Lk) (P : monPred I PROP) :
    ObjectiveWith Lk P ->
    ObjectiveWith (Lj .+_{D} Lk) (<obj>_{Lj} P).
  Proof.
    intros OBJ i [j k]. rewrite !monPred_at_forall /=.
    setoid_rewrite D.
    setoid_rewrite mlens_set_set.
    setoid_rewrite <-D.
    iIntros "P" (j'). iApply OBJ. by iApply "P".
  Qed.

  Lemma monPred_objectively_with_objective_with_disjoint_right
    {PROP: bi} (Lj : MLens I J) (Lk : MLens I K)
    (D: Lk .## Lj) (P : monPred I PROP) :
    ObjectiveWith Lk P ->
    ObjectiveWith (Lk .+_{D} Lj) (<obj>_{Lj} P).
  Proof.
    intros OBJ i [j k]. rewrite !monPred_at_forall /=.
    setoid_rewrite mlens_set_set.
    setoid_rewrite D.
    iIntros "P" (j'). iApply OBJ. by iApply "P".
  Qed.

  Lemma monPred_objective_with_join
    {PROP: bi} (Lj : MLens I J) (Lk : MLens I K)
    (D: Lj .## Lk) (P : monPred I PROP) :
    ObjectiveWith Lj P -> ObjectiveWith Lk P ->
    ObjectiveWith (Lj .+_{D} Lk) P.
  Proof.
    intros Oj Ok i [j k]. rewrite /=. iIntros "P". iApply Ok. by iApply Oj.
  Qed.
End mlens_prod.

Section bi_prod.
  Context {I J K: biIndex}.
  Implicit Types (L : MLens I (J *i K)).

  Lemma monPred_exactly_with_objective_with_left
    {PROP: bi} L (P : monPred I PROP) j :
    ObjectiveWith (L.r) P ->
    ObjectiveWith L (@(L.l, j) P).
  Proof.
    intros.
    apply (monPred_objective_with_lens_equiv _ _ _ (mlens_equiv_split_join L)).
    by apply monPred_exactly_at_objective_with_disjoint_left.
  Qed.

  Lemma monPred_exactly_with_objective_with_right
    {PROP: bi} L (P : monPred I PROP) k :
    ObjectiveWith (L.l) P ->
    ObjectiveWith L (@(L.r, k) P).
  Proof.
    intros.
    apply (monPred_objective_with_lens_equiv _ _ _ (mlens_equiv_split_join L)).
    by apply monPred_exactly_at_objective_with_disjoint_right.
  Qed.

  Lemma monPred_objectively_with_objective_with_left
    {PROP: bi} L (P : monPred I PROP) :
    ObjectiveWith (L.r) P ->
    ObjectiveWith L (<obj>_{L.l} P).
  Proof.
    intros.
    apply (monPred_objective_with_lens_equiv _ _ _ (mlens_equiv_split_join L)).
    by apply monPred_objectively_with_objective_with_disjoint_left.
  Qed.

  Lemma monPred_objectively_with_objective_with_right
    {PROP: bi} L (P : monPred I PROP) :
    ObjectiveWith (L.l) P ->
    ObjectiveWith L (<obj>_{L.r} P).
  Proof.
    intros.
    apply (monPred_objective_with_lens_equiv _ _ _ (mlens_equiv_split_join L)).
    by apply monPred_objectively_with_objective_with_disjoint_right.
  Qed.

  Lemma monPred_objective_with_join_lr
    {PROP: bi} L (P : monPred I PROP) :
    ObjectiveWith (L.l) P -> ObjectiveWith (L.r) P ->
    ObjectiveWith L P.
  Proof.
    intros.
    apply (monPred_objective_with_lens_equiv _ _ _ (mlens_equiv_split_join L)).
    by apply monPred_objective_with_join.
  Qed.
End bi_prod.
