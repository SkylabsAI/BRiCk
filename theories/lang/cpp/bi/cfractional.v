(*
 * Copyright (c) 2022-2023 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bedrock.lang.cpp.algebra.cv.
From bedrock.lang.bi Require Import prelude observe fractional.
From bedrock.lang.cpp.bi Require Import split_cv.
Require Import iris.proofmode.proofmode.
Import ChargeNotation.

#[local] Set Printing Coercions.

(** * Fractional predicates at type [CV.t] *)
(**
Overview:

- [CFractional], [AsCFractional] enable one to declare predicates that
are fractional at type [CV.t]

- Tactic [solve_as_cfrac] for solving [AsCFractional]

- [CFractionalN], [AsCFractionalN], [CFracValidN], [CFrac2ValidN],
[AgreeCF1] notation to save typing

- [IntoSep], [FromSep] instances teaching the IPM to split and combine
[CFractional] predicates
*)

(** Proof obligation for const/mutable fractional things. *)
Class CFractional {PROP : bi} (P : CV.t -> PROP) : Prop :=
  cfractional q1 q2 : P (q1 ⋅ q2) -|- P q1 ** P q2.
#[global] Hint Mode CFractional + ! : typeclass_instances.
#[global] Arguments CFractional {_} _%I : simpl never, assert.

(**
[CFractionalN] states that predicate [P] taking a const/mutable
fraction and then [N] arguments is [CFractional]
*)
Notation CFractional1 P := (∀ a, CFractional (fun q => P q a)) (only parsing).
Notation CFractional2 P := (∀ a b, CFractional (fun q => P q a b)) (only parsing).
Notation CFractional3 P := (∀ a b c, CFractional (fun q => P q a b c)) (only parsing).
Notation CFractional4 P := (∀ a b c d, CFractional (fun q => P q a b c d)) (only parsing).
Notation CFractional5 P := (∀ a b c d e, CFractional (fun q => P q a b c d e)) (only parsing).

(** [CFractional] wrapper suited to avoiding HO unification. *)
#[projections(primitive)]
Class AsCFractional {PROP : bi} (P : PROP) (Q : CV.t -> PROP) (cv : CV.t) : Prop := {
  as_cfractional : P -|- Q cv;
  as_cfractional_cfractional :> CFractional Q;
}.
#[global] Hint Mode AsCFractional + ! - - : typeclass_instances.
#[global] Hint Mode AsCFractional + - + - : typeclass_instances.
#[global] Arguments AsCFractional {_} (_ _)%I _%Qp : assert.

Ltac solve_as_cfrac := solve [intros; exact: Build_AsCFractional].

(** [AsCFractionalN] informs the IPM about predicate [P] satisfying [CFractionalN P] *)
Notation AsCFractional0 P := (∀ q, AsCFractional (P q) P q) (only parsing).
Notation AsCFractional1 P := (∀ q a, AsCFractional (P q a) (fun q => P%I q a) q) (only parsing).
Notation AsCFractional2 P := (∀ q a b, AsCFractional (P q a b) (fun q => P%I q a b) q) (only parsing).
Notation AsCFractional3 P := (∀ q a b c, AsCFractional (P q a b c) (fun q => P%I q a b c) q) (only parsing).
Notation AsCFractional4 P := (∀ q a b c d, AsCFractional (P q a b c d) (fun q => P%I q a b c d) q) (only parsing).
Notation AsCFractional5 P := (∀ q a b c d e, AsCFractional (P q a b c d e) (fun q => P%I q a b c d e) q) (only parsing).

(**
[AgreeCF1 P] states that [P q a] only holds for one possible [a],
regardless of const/mutable fraction [q].
*)
Notation AgreeCF1 P := (∀ (q1 q2 : CV.t) a1 a2, Observe2 [| a1 = a2 |] (P q1 a1) (P q2 a2)) (only parsing).

(**
[FracEq q1 q2] normalizes [q1] to [q2].
This helps TC search reduce TC-opaque [CV.frac] in a controlled way.
Used to state [CFracValidN].

TODO: Reformulate as [CVToFrac (cv : CV.t) (q : Qp)] to disentangle
reduction from the initial projection [CV.frac cv], and drop those
projections from the following [CFracValidN] notations. We'll want a
second reduction rule covering [CV.scale] once that becomes a
constant.
*)
#[projections(primitive=yes)]
Class FracEq (q1 q2 : Qp) := MkFracEq { frac_eq : q1 = q2 }.
#[global] Hint Mode FracEq + - : typeclass_instances.
Arguments MkFracEq {_ _} _ : assert.
Arguments frac_eq {_ _} _ : assert.

Lemma frac_eq_iff q1 q2 : FracEq q1 q2 <-> q1 = q2.
Proof. split. by inversion_clear 1. by intros ->. Qed.

#[global] Instance frac_eq_beta_reduce q qout c :
  FracEq q qout ->
  FracEq (CV.frac (CV.mk c q)) qout | 20.
Proof. by intros ->%frac_eq. Qed.

(* Higher cost, to favor [frac_eq_beta_reduce]. *)
#[global] Instance frac_eq_refl (q : Qp) : FracEq q q | 50.
Proof. done. Qed.

(**
[CFracValidN P] observes [CV.frac q ≤ 1] from [P] applied to
const/mutable fraction [q] and then [N] arguments.
*)
Notation CFracValid0 P := (∀ (q : CV.t) (p : Qp), FracEq (CV.frac q) p ->
  Observe [| p ≤ 1 |]%Qp (P q)) (only parsing).
Notation CFracValid1 P := (∀ (q : CV.t) (p : Qp), FracEq (CV.frac q) p ->
  ∀ a, Observe [| p ≤ 1 |]%Qp (P q a)) (only parsing).
Notation CFracValid2 P := (∀ (q : CV.t) (p : Qp), FracEq (CV.frac q) p ->
  ∀ a b, Observe [| p ≤ 1 |]%Qp (P q a b)) (only parsing).
Notation CFracValid3 P := (∀ (q : CV.t) (p : Qp), FracEq (CV.frac q) p ->
  ∀ a b c, Observe [| p ≤ 1 |]%Qp (P q a b c)) (only parsing).
Notation CFracValid4 P := (∀ (q : CV.t) (p : Qp), FracEq (CV.frac q) p ->
  ∀ a b c d, Observe [| p ≤ 1 |]%Qp (P q a b c d)) (only parsing).
Notation CFracValid5 P := (∀ (q : CV.t) (p : Qp), FracEq (CV.frac q) p ->
  ∀ a b c d e, Observe [| p ≤ 1 |]%Qp (P q a b c d e)) (only parsing).

(**
[CFrac2ValidN P] is a useful corollary of [CFracValidN], observing
[CV.frac q1 + CV.frac q2 ≤ 1] given [P q1 a1 .. aN ** P q2 b1 .. bN].
*)
Notation CFrac2Valid0 P := (∀ q1 q2, Observe2 [| CV.frac q1 + CV.frac q2 ≤ 1 |]%Qp (P q1) (P q2)) (only parsing).
Notation CFrac2Valid1 P := (∀ q1 q2 a1 a2, Observe2 [| CV.frac q1 + CV.frac q2 ≤ 1 |]%Qp (P q1 a1) (P q2 a2)) (only parsing).

Section cfractional.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP).

  (** ** Properties of [CFractional] *)

  #[global] Instance: Params (@CFractional) 1 := {}.
  #[global] Instance CFractional_proper :
    Proper (pointwise_relation _ (equiv (A:=PROP)) ==> iff) CFractional.
  Proof.
    intros P1 P2 EQ. split=>Frac cv1 cv2.
    by rewrite -EQ Frac. by rewrite EQ Frac.
  Qed.

  (** ** Compatiblity for [CFractional] *)

  #[global] Instance persistent_cfractional `{!Persistent P, !TCOr (Affine P) (Absorbing P)} :
    CFractional (fun _ => P).
  Proof.
    rewrite /CFractional=>cv1 cv2.
    by rewrite {1}(bi.persistent_sep_dup P).
  Qed.

  #[global] Instance cfractional_sep (F G : CV.t -> PROP) :
    CFractional F -> CFractional G ->
    CFractional (fun cv => F cv ** G cv).
  Proof.
    rewrite /CFractional=>HF HG cv1 cv2. rewrite {}HF {}HG.
    split'; iIntros "([$ $] & $ & $)".
  Qed.

  #[global] Instance cfractional_exist {A} (P : A -> CV.t -> PROP) :
    (∀ oa, CFractional (P oa)) ->
    (∀ a1 a2 q1 q2, Observe2 [| a1 = a2 |] (P a1 q1) (P a2 q2)) ->
    CFractional (fun q => Exists a : A, P a q).
  Proof.
    intros ?? q1 q2.
    rewrite -bi.exist_sep; last by intros; exact: observe_2_elim_pure.
    f_equiv=>oa. apply: cfractional.
  Qed.

  #[global] Instance cfractional_embed `{!BiEmbed PROP PROP'} F :
    CFractional F -> CFractional (fun q => embed (F q) : PROP').
  Proof. intros ???. by rewrite cfractional embed_sep. Qed.

  (**
  TODO: If this is really needed, add a comment explaining why. It's
  somewhat surprising.
  *)
  Lemma as_cfractional_embed `{!BiEmbed PROP PROP'} P F q :
    AsCFractional P F q -> AsCFractional (embed P) (fun q => embed (F q)) q.
  Proof. split; [by rewrite ->!as_cfractional | apply _]. Qed.

  #[global] Instance cfractional_big_sepL {A} (l : list A) F :
    (∀ k x, CFractional (F k x)) ->
    CFractional (PROP:=PROP) (funI q => [** list] k |-> x ∈ l, F k x q).
  Proof. intros ? q q'. rewrite -big_sepL_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepL2 {A B} (l1 : list A) (l2 : list B) F :
    (∀ k x1 x2, CFractional (F k x1 x2)) ->
    CFractional (PROP:=PROP) (funI q => [∗ list] k↦x1; x2 ∈ l1; l2, F k x1 x2 q).
  Proof. intros ? q q'. rewrite -big_sepL2_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepM `{Countable K} {A} (m : gmap K A) F :
    (∀ k x, CFractional (F k x)) ->
    CFractional (PROP:=PROP) (funI q => [** map] k |-> x ∈ m, F k x q).
  Proof. intros ? q q'. rewrite -big_sepM_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepS `{Countable A} (X : gset A) F :
    (∀ x, CFractional (F x)) ->
    CFractional (PROP:=PROP) (funI q => [** set] x ∈ X, F x q).
  Proof. intros ? q q'. rewrite -big_sepS_sep. by setoid_rewrite cfractional. Qed.

  #[global] Instance cfractional_big_sepMS `{Countable A} (X : gmultiset A) F :
    (∀ x, CFractional (F x)) ->
    CFractional (PROP:=PROP) (funI q => [** mset] x ∈ X, F x q).
  Proof. intros ? q q'. rewrite -big_sepMS_sep. by setoid_rewrite cfractional. Qed.

  (** *** Lifting [Fractional] things via [CV.frac]. *)

  #[global] Instance fractional_cfractional_0 (P : Qp -> PROP) :
    Fractional P -> CFractional (fun q => P (CV.frac q)).
  Proof. intros HP ??. rewrite CV.t_op /=. apply HP. Qed.
  #[global] Instance fractional_cfractional_1 {A} (P : Qp -> A -> PROP) :
    Fractional1 P -> CFractional1 (fun q a => P (CV.frac q) a).
  Proof. intros HP ???. rewrite CV.t_op /=. apply HP. Qed.
  #[global] Instance fractional_cfractional_2 {A B} (P : Qp -> A -> B -> PROP) :
    Fractional2 P -> CFractional2 (fun q a b => P (CV.frac q) a b).
  Proof. intros HP ????. rewrite CV.t_op /=. apply HP. Qed.
  #[global] Instance fractional_cfractional_3 {A B C} (P : Qp -> A -> B -> C -> PROP) :
    Fractional3 P -> CFractional3 (fun q a b c => P (CV.frac q) a b c).
  Proof. intros HP ?????. rewrite CV.t_op /=. apply HP. Qed.
  #[global] Instance fractional_cfractional_4 {A B C D} (P : Qp -> A -> B -> C -> D -> PROP) :
    Fractional4 P -> CFractional4 (fun q a b c d => P (CV.frac q) a b c d).
  Proof. intros HP ??????. rewrite CV.t_op /=. apply HP. Qed.
  #[global] Instance fractional_cfractional_5 {A B C D E} (P : Qp -> A -> B -> C -> D -> E ->PROP) :
    Fractional5 P -> CFractional5 (fun q a b c d e => P (CV.frac q) a b c d e).
  Proof. intros HP ???????. rewrite CV.t_op /=. apply HP. Qed.

  (** *** Lifting [CFractional] things when using [CV.mk]. *)
  #[global] Instance cfractional_cfractional_mk_0 (P : CV.t -> PROP) c :
    CFractional P -> CFractional (fun q => P (CV.mk c (CV.frac q))).
  Proof. intros HP ??. rewrite CV.t_op /= CV.mk_add. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_1 {A} (P : CV.t -> A -> PROP) c :
    CFractional1 P -> ∀ a, CFractional (fun q => P (CV.mk c (CV.frac q)) a).
  Proof. intros HP ???. rewrite CV.t_op /= CV.mk_add. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_2 {A B} (P : CV.t -> A -> B -> PROP) cm :
    CFractional2 P -> ∀ a b, CFractional (fun q => P (CV.mk cm (CV.frac q)) a b).
  Proof. intros HP ????. rewrite CV.t_op /= CV.mk_add. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_3 {A B C} (P : CV.t -> A -> B -> C -> PROP) cm :
    CFractional3 P -> ∀ a b c, CFractional (fun q => P (CV.mk cm (CV.frac q)) a b c).
  Proof. intros HP ?????. rewrite CV.t_op /= CV.mk_add. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_4 {A B C D} (P : CV.t -> A -> B -> C -> D -> PROP) cm :
    CFractional4 P -> ∀ a b c d, CFractional (fun q => P (CV.mk cm (CV.frac q)) a b c d).
  Proof. intros HP ??????. rewrite CV.t_op /= CV.mk_add. apply HP. Qed.

  #[global] Instance cfractional_cfractional_mk_5 {A B C D E} (P : CV.t -> A -> B -> C -> D -> E -> PROP) cm :
    CFractional5 P -> ∀ a b c d e, CFractional (fun q => P (CV.mk cm (CV.frac q)) a b c d e).
  Proof. intros HP ???????. rewrite CV.t_op /= CV.mk_add. apply HP. Qed.
End cfractional.

(** ** Backwards compatibility *)
(**
The following instances are only needed for backward compatibility,
when using [CFractional] [Rep]s in [Fractional] ones, so we only
support [CV._mut] not [CV.const] (or [CV.mut]).
*)
Module CV_compat.
  Export cv.CV_compat.

  Section cfractional.
    Context {PROP : bi}.
    Implicit Types (P Q : PROP).

    (** *** Lifting [CFractional] things into [Fractional] when using [CV._mut] *)

    #[export] Instance cfractional_fractional_mut_0 (P : CV.t -> PROP) :
      CFractional P -> Fractional P.
    Proof. intros HP ??. rewrite /= CV.mk_add. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_1 {A} (P : CV.t -> A -> PROP) :
      CFractional1 P -> Fractional1 P.
    Proof. intros HP ???. rewrite /= CV.mk_add. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_2 {A B} (P : CV.t -> A -> B -> PROP) :
      CFractional2 P -> Fractional2 P.
    Proof. intros HP ????. rewrite /= CV.mk_add. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_3 {A B C} (P : CV.t -> A -> B -> C -> PROP) :
      CFractional3 P -> Fractional3 P.
    Proof. intros HP ?????. rewrite /= CV.mk_add. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_4 {A B C D} (P : CV.t -> A -> B -> C -> D -> PROP) :
      CFractional4 P -> Fractional4 P.
    Proof. intros HP ??????. rewrite /= CV.mk_add. apply HP. Qed.

    #[export] Instance cfractional_fractional_mut_5 {A B C D E} (P : CV.t -> A -> B -> C -> D -> E -> PROP) :
      CFractional5 P -> Fractional5 P.
    Proof. intros HP ???????. rewrite /= CV.mk_add. apply HP. Qed.

  End cfractional.

End CV_compat.

(* TEMPORARY: Re-export [CV_compat] for now. *)
Export CV_compat.

(** ** IPM instances *)
Section proofmode.
  Context {PROP : bi}.
  Implicit Types (P Q : PROP) (F G : CV.t -> PROP).

  #[local] Lemma as_cfractional_split P P1 P2 F cv cv1 cv2 :
    AsCFractional P F cv -> SplitCV cv cv1 cv2 ->
    AsCFractional P1 F cv1 -> AsCFractional P2 F cv2 ->
    P -|- P1 ** P2.
  Proof.
    intros [->?] ? [->_] [->_]. by rewrite (split_cv cv) cfractional.
  Qed.

  #[local] Lemma as_cfractional_combine P1 P2 P F cv1 cv2 cv :
    AsCFractional P1 F cv1 -> AsCFractional P2 F cv2 ->
    CombineCV cv1 cv2 cv -> AsCFractional P F cv ->
    P -|- P1 ** P2.
  Proof.
    intros [->?] [->_] ? [->_]. by rewrite -cfractional combine_cv.
  Qed.

  (**
  Support the IPM's [P1 P2] intro pattern: [P] an input; [P1], [P2]
  outputs.
  *)

  #[global] Instance into_sep_cfractional P P1 P2 F cv cv1 cv2 :
    AsCFractional P F cv -> SplitCV cv cv1 cv2 ->
    AsCFractional P1 F cv1 -> AsCFractional P2 F cv2 ->
    IntoSep P P1 P2.
  Proof.
    intros. rewrite/IntoSep. by rewrite (as_cfractional_split P).
  Qed.

  (**
  Support the IPM's [iSplitL], [iSplitR] tactics: [P] an input; [P1],
  [P2] outputs.
  *)
  #[global] Instance from_sep_cfractional_split P P1 P2 F cv cv1 cv2 :
    AsCFractional P F cv -> SplitCV cv cv1 cv2 ->
    AsCFractional P1 F cv1 -> AsCFractional P2 F cv2 ->
    FromSep P P1 P2.
  Proof.
    intros. rewrite/FromSep. by rewrite -(as_cfractional_split P).
  Qed.

  (**
  Support the IPM's [iCombine] tactic: [P1], [P2] inputs, [P] an
  output.

  This instance has a higher cost so it doesn't interfere with
  [iSplitL], [iSplitR]. (Overall, things might be simpler if the IPM
  used a dedicated class for combining.)
  *)
  #[global] Instance from_sep_cfractional_combine P1 P2 P F cv1 cv2 cv :
    AsCFractional P1 F cv1 -> AsCFractional P2 F cv2 ->
    CombineCV cv1 cv2 cv -> AsCFractional P F cv ->
    FromSep P P1 P2 | 100.
  Proof.
    intros. rewrite/FromSep. by rewrite -as_cfractional_combine.
  Qed.

End proofmode.
