(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.ssr.ssreflect.
Require Import stdpp.prelude.
Require Import iris.bi.monpred. (* ==> for biIndex only. *)

Set Default Proof Using "Type".
Set Suggest Proof Using.

Implicit Types (I J K : biIndex).

(* Monotone lens from I to J. Get and Set are required to preserve monotonicity. *)
Structure MLens {I J : biIndex} : Type := MLensMake {
  mlens_get : I -> J ;
  mlens_set : J -> I -> I ;
  mlens_get_mono : Proper ((⊑) ==> (⊑)) mlens_get ;
  mlens_set_mono : Proper ((⊑) ==> (⊑) ==> (⊑)) mlens_set ;
  mlens_get_set : forall i j, mlens_get (mlens_set j i) = j ;
  mlens_set_get : forall i, mlens_set (mlens_get i) i = i ;
  mlens_set_set : forall i j1 j2, mlens_set j1 (mlens_set j2 i) = mlens_set j1 i ;
}.

Arguments MLens : clear implicits.

Notation "L '.=' j" := (mlens_set L j) (at level 49, left associativity, format "L  .=  j") : stdpp_scope.
Notation "i '.^' L" := (mlens_get L i) (at level 45, left associativity, format "i .^ L") : stdpp_scope.

(* TODO: seal all of these lens operations. *)
Program Definition MLid {I} : MLens I I := {|
  mlens_get := fun i => i;
  mlens_set := fun j i => j;
|}.
Next Obligation. by intros ??? L ???. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Local Hint Extern 2 (mlens_get _ _ ⊑ mlens_get _ _) => apply : mlens_get_mono : core.
Local Hint Extern 2 (mlens_set _ _ _ ⊑ mlens_set _ _ _) => apply : mlens_set_mono : core.

(* Lj .>> Lk *)
(* Gordon used the notation .@, but this is clashing with namespaces
  subnamespacing, so I opted to use this notation .>>*)
Program Definition MLens_compose {I J K}
  (Lj : MLens I J) (Lk : MLens J K) : MLens I K :=
{|
  mlens_get := fun i => i.^Lj.^Lk ;
  mlens_set := fun k i => (Lj .= (Lk .= k) (i.^Lj)) i ;
|}.
Next Obligation. intros ???  ?? ???. auto. Qed.
Next Obligation. intros ??? ?? ??? ???. auto. Qed.
Next Obligation. intros. by rewrite /= !mlens_get_set. Qed.
Next Obligation. intros. by rewrite /= !mlens_set_get. Qed.
Next Obligation. intros. by rewrite /= !mlens_get_set !mlens_set_set. Qed.
Infix ".>>" := MLens_compose (at level 45, left associativity) : stdpp_scope.
Notation "(.>>)" := MLens_compose (only parsing) : stdpp_scope.

(* L1 .== L2 *)
Record MLens_eq {I J} (L1 L2: MLens I J) := mkMLensEq {
  mlens_eq_get i : i.^L1 = i.^L2 ;
  mlens_eq_set i j : (L1 .= j) i = (L2 .= j) i;
}.
Infix ".==" := MLens_eq (at level 70) : stdpp_scope.
Notation "(.==)" := MLens_eq (only parsing) : stdpp_scope.

(* Lj .<= Lk *)
Definition MLens_le {I J K} (Lj: MLens I J) (Lk: MLens I K) : Prop :=
  ∃ (L : MLens K J), Lj .== Lk .>> L.
Infix ".<=" := MLens_le (at level 70) : stdpp_scope.
Notation "(.<=)" := MLens_le (only parsing) : stdpp_scope.

(* Lj .≡ Lk *)
Definition MLens_equiv {I J K} (Lj: MLens I J) (Lk: MLens I K) :=
  MLens_le Lj Lk /\ MLens_le Lk Lj.
Infix ".≡" := MLens_equiv (at level 70) : stdpp_scope.
Notation "(.≡)" := MLens_equiv (only parsing) : stdpp_scope.

(* Lj .## Lk *)
Definition MLens_disjoint {I J K} (Lj: MLens I J) (Lk: MLens I K) :=
  ∀ i j k, (Lk .= k) ((Lj .= j) i) = (Lj .= j) ((Lk .= k) i).
Infix ".##" := MLens_disjoint (at level 70) : stdpp_scope.
Notation "(.##)" := MLens_disjoint (only parsing) : stdpp_scope.
(* TODO suggested by Paolo :
  This swap law should strengthen to "sublenses" of Lj and Lk by
  definition: MLens_disjoint Lj Lk := ∀ Lj1 Lk2, Lj1 .<= Lj -> Lk1 .<= Lj -> ... *)

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

Program Definition MLens_fst {I J} : MLens (I *i J) I := {|
  mlens_get := fun ij => ij.1;
  mlens_set := fun i ij => (i, ij.2);
|}.
Next Obligation. intros ?? ??? [][][]. split; auto. Qed.
Next Obligation. by intros ?? []. Qed.
Next Obligation. by intros ?? []. Qed.
Next Obligation. by intros ?? []. Qed.

Program Definition MLens_snd {I J} : MLens (I *i J) J := {|
  mlens_get := fun ij => ij.2;
  mlens_set := fun j ij => (ij.1, j);
|}.
Next Obligation. intros ?? ??? [][][]. split; auto. Qed.
Next Obligation. by intros ?? []. Qed.
Next Obligation. by intros ?? []. Qed.
Next Obligation. by intros ?? []. Qed.

Definition MLens_left {I J K} (L: MLens I (J *i K)) : MLens I J := L .>> MLens_fst.
Definition MLens_right {I J K} (L: MLens I (J *i K)) : MLens I K := L .>> MLens_snd.

Notation "L '.l'" := (MLens_left L)
  (at level 61, left associativity, format "L .l"): stdpp_scope.
Notation "L '.r'" := (MLens_right L)
  (at level 61, left associativity, format "L .r"): stdpp_scope.


Program Definition MLens_join {I J K}
  (Lj: MLens I J) (Lk: MLens I K) (DISJ: Lj .## Lk)
  : MLens I (J *i K) := {|
    mlens_get := fun i => (i.^Lj, i.^Lk);
    mlens_set := fun jk i => (Lk .= jk.2) ((Lj .= jk.1) i);
  |}.
Next Obligation. intros ??? ?? ? ???. split; simpl; auto. Qed.
Next Obligation. intros ??? ??? [] [] [] ???. simpl; auto. Qed.
Next Obligation.
  intros ??? ??? ? []. by rewrite /= mlens_get_set DISJ mlens_get_set. Qed.
Next Obligation. intros ??? ??? ?. by rewrite /= !mlens_set_get. Qed.
Next Obligation.
  intros ??? ???? [][]. by rewrite /= DISJ mlens_set_set DISJ mlens_set_set DISJ. Qed.

Notation "Lj '.+_{' D '}' Lk" := (MLens_join Lj Lk D)
  (at level 65, format "Lj  .+_{ D }  Lk"): stdpp_scope.

(* MLens_eq *)
Instance mlens_eq_equivalence {I J} : Equivalence (@MLens_eq I J).
Proof.
  constructor.
  - intros ?; by constructor.
  - intros ?? [??]; by constructor.
  - intros ??? [EG1 ES1] [EG2 ES2]; constructor.
    + intros. by rewrite EG1 EG2.
    + intros. by rewrite ES1 ES2.
Qed.

Instance mlens_eq_get_proper {I J} :
  Proper ((.==) ==> (=) ==> (=)) (@mlens_get I J).
Proof. intros L1 L2 [Eq1 Eq2] i1 i2 ->. by rewrite Eq1. Qed.
Instance mlens_eq_set_proper {I J} :
  Proper ((.==) ==> (=) ==> (=) ==> (=)) (@mlens_set I J).
Proof. intros L1 L2 [Eq1 Eq2] i1 i2 -> j1 j2 ->. by rewrite Eq2. Qed.
Instance : Params (@mlens_get) 2 := {}.
Instance : Params (@mlens_set) 2 := {}.

(* MLens_compose *)
(* We would like instances here, like LeftId, RightId, Assoc, but the types of
  lenses do not fit into `relation A` of the same `A` *)
Lemma mlens_compose_id_l {I J} (L: MLens I J) : L .== L .>> MLid.
Proof. by constructor. Qed.
Lemma mlens_compose_id_r {I J} (L: MLens I J) : L .== MLid .>> L.
Proof. by constructor. Qed.

Lemma mlens_compose_assoc {I J K H}
  (Lj : MLens I J) (Lk : MLens J K) (Lh : MLens K H) :
  Lj .>> Lk .>> Lh .== Lj .>> (Lk .>> Lh).
Proof. by constructor. Qed.

Instance mlens_eq_compose_proper {I J K} :
  Proper ((.==) ==> (.==) ==> (.==)) (@MLens_compose I J K).
Proof.
  intros Lj1 Lj2 [Eqj1 Eqj2] Lk1 Lk2 [Eqk1 Eqk2].
  constructor; intros.
  - by rewrite /= Eqj1 Eqk1.
  - by rewrite /= Eqj2 Eqk2 Eqj1.
Qed.
Instance : Params (@MLens_compose) 3 := {}.

(* MLens_le *)

Lemma mlens_le_id {I J} (L: MLens I J) : L .<= MLid.
Proof. exists L. by apply mlens_compose_id_r. Qed.

Instance mlens_eq_le_proper {I J K} :
  Proper ((@MLens_eq I J) ==> (@MLens_eq I K) ==> (impl)) (@MLens_le I J K).
Proof. intros ?? Eqj ?? Eqk [Lj Eq]. exists Lj. by rewrite -Eqj Eq Eqk. Qed.
(* le is not Proper w.r.t compose *)
Instance : Params (@MLens_le) 3 := {}.

(* MLens_le is a Pre-Order. *)
Instance mlens_le_reflexive {I J} : Reflexive (@MLens_le I J J).
Proof. intros L. exists MLid. apply mlens_compose_id_l. Qed.

(* Can't state this with Transitive. *)
Lemma mlens_le_transitive {I J K H}
  (Lj : MLens I J) (Lk : MLens I K) (Lh : MLens I H) :
  Lj .<= Lk -> Lk .<= Lh -> Lj .<= Lh.
Proof.
  intros [L1 Le1] [L2 Le2]. exists (L2 .>> L1).
  by rewrite Le1 Le2 mlens_compose_assoc.
Qed.

Lemma mlens_le_get {I J K} (Lj: MLens I J) (Lk: MLens I K) :
  Lj .<= Lk -> ∀ i1 i2, i1.^Lk = i2.^Lk -> i1.^Lj = i2.^Lj.
Proof. intros [Lm [Eq1 Eq2]] i1 i2 Eqk. by rewrite !Eq1 /= Eqk. Qed.

Lemma mlens_le_set_inner {I J K} (Lj: MLens I J) (Lk: MLens I K) i j :
  Lj .<= Lk -> (Lk .= ((Lj .= j) i.^Lk)) i = (Lj .= j) i.
Proof. intros [Lm [Eq1 Eq2]]. by rewrite Eq2 mlens_get_set. Qed.

Lemma mlens_le_set_outer {I J K} (Lj: MLens I J) (Lk: MLens I K) i j k :
  Lj .<= Lk -> (Lk .= k) ((Lj .= j) i) = (Lk .= k) i.
Proof. intros [Lm [Eq1 Eq2]]. by rewrite Eq2 mlens_set_set. Qed.

(* MLens_equiv *)
(* MLens_equiv is an equivalence *)
Instance mlens_equiv_reflexive {I J} : Reflexive (@MLens_equiv I J J).
Proof. done. Qed.

(* Can't state as a Symmetric instance *)
Lemma mlens_equiv_symmetric {I J K} (Lj : MLens I J) (Lk : MLens I K) :
  Lj .≡ Lk <-> Lk .≡ Lj.
Proof. rewrite /MLens_equiv. intuition. Qed.
(* Weaker instance where J = K *)
Instance mlens_equiv_symmetric' {I J} : Symmetric (@MLens_equiv I J J).
Proof. intros ??. by apply mlens_equiv_symmetric. Qed.

(* Can't state as a Transitive instance *)
Lemma mlens_equiv_transitive {I J K H}
  (Lj : MLens I J) (Lk : MLens I K) (Lh : MLens I H) :
  Lj .≡ Lk -> Lk .≡ Lh -> Lj .≡ Lh.
Proof. intros [Le1 Le2] [Le3 Le4]. split; eapply mlens_le_transitive; eauto. Qed.
(* Weaker instance where J = K *)
Instance mlens_equiv_transitive' {I J} : Transitive (@MLens_equiv I J J).
Proof. intros ???. by apply mlens_equiv_transitive. Qed.

Instance mlens_eq_equiv_sub {I J} : subrelation (@MLens_eq I J) (@MLens_equiv I J J).
Proof. intros ?? Eq. split; by rewrite Eq. Qed.

Lemma mlens_equiv_le_sub {I J K} (Lj : MLens I J) (Lk : MLens I K) :
  Lj .≡ Lk -> Lj .<= Lk.
Proof. by intros []. Qed.
Instance mlens_equiv_le_sub' {I J} : subrelation (@MLens_equiv I J J) (@MLens_le I J J).
Proof. intros ??. by apply mlens_equiv_le_sub. Qed.

(* MLens_disjoint *)
Lemma mlens_disjoint_symmetric {I J K} (Lj: MLens I J) (Lk: MLens I K) :
  Lj .## Lk <-> Lk .## Lj.
Proof. split; intros DISJ ???; by rewrite DISJ. Qed.

Lemma mlens_disjoint_get_set {I J K} (Lj: MLens I J) (Lk: MLens I K)
  (DISJ: Lj .## Lk) :
  forall i j, ((Lj .= j) i).^Lk = i.^Lk.
Proof.
  intros i j. by rewrite -{1}(mlens_set_get Lk i) -DISJ mlens_get_set.
Qed.

Lemma mlens_set_reset_order {I J} (L: MLens I J) i i' j :
  (L .= j) i ⊑ i' -> i ⊑ (L .= (i.^L)) i'.
Proof.
  intros Le. rewrite -{1}(mlens_set_get L i)-(mlens_set_set _ i _ j).
  apply mlens_set_mono; auto.
Qed.

Instance mlens_disjoint_eq_proper {I J K}:
  Proper ((@MLens_eq I J) ==> (@MLens_eq I K) ==> (impl)) (@MLens_disjoint I J K).
Proof.
  intros Lj1 Lj2 [Eqj1 Eqj2] Lk1 Lk2 [Eqk1 Eqk2].
  rewrite /MLens_disjoint => DISJ i j k.
  by rewrite -Eqj2 -Eqk2 DISJ Eqj2 Eqk2.
Qed.
Instance : Params (@MLens_disjoint) 3 := {}.

(* TODO: this one doesn't seem to hold, probably because the characterization of
  MLens_le/MLens_disjoint is too weak. *)
(* This can't be stated as a Proper instance, because all the lenses are of
  different types. *)
Lemma mlens_disjoint_le {I J K J1 K1}
  (Lj : MLens I J) (Lk : MLens I K) (Lj1 : MLens I J1) (Lk1 : MLens I K1) :
  Lj .## Lk -> Lj1 .<= Lj -> Lk1 .<= Lk -> Lj1 .## Lk1.
Abort.

Lemma mlens_le_left {I J K} (L : MLens I (J *i K)) : L.l .<= L.
Proof. by eexists. Qed.

Lemma mlens_le_right {I J K} (L : MLens I (J *i K)) : L.r .<= L.
Proof. by eexists. Qed.

Lemma mlens_disjoint_prod {I J K} (L : MLens I (J *i K)) :
  L.l .## L.r.
Proof. intros i j k. by rewrite /= !mlens_get_set /= !mlens_set_set. Qed.

Lemma mlens_eq_split_join {I J K} (L : MLens I (J *i K)) :
  L .== L.l .+_{mlens_disjoint_prod L} L.r.
Proof.
  constructor; simpl.
  - intros i. by destruct (i.^L).
  - intros i [j k]. by rewrite /= !mlens_get_set !mlens_set_set.
Qed.

(* Stupid non-general lemma because I can't prove mlens_disjoint_le *)
Lemma mlens_disjoint_prod_l_rl {I J K H} (L : MLens I (J *i K *i H)) :
  L.l .## L.r.l.
Proof. intros i j k. by rewrite /= !mlens_get_set /= !mlens_set_set. Qed.
