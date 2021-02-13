(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(*
 * Some of the following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/ecad6c9fc48752b52678119c923dc4fff8e96f15/LICENSE-CODE
 *)
From stdpp Require Import coPset.
Require Import iris.bi.bi.

(* A simplification of monPred that assumes equality on the argument. TODO: try dropping the sealing. *)
(* TODO: undo the sealing. *)

#[local] Set Default Proof Using "Type".
#[local] Set Suggest Proof Using.

Structure biIndex :=
  BiIndex
    { bi_index_type :> Type;
      bi_index_inhabited : Inhabited bi_index_type; }.
Existing Instances bi_index_inhabited.

Record monPred {I : biIndex} {PROP : bi} :=
  MonPred { monPred_at :> I → PROP }.
Bind Scope bi_scope with monPred.

#[global] Arguments monPred _ _ : clear implicits, assert.
#[global] Arguments MonPred {_ _} _%I : assert.
(* Simplification! *)
#[global] Arguments monPred_at {I} {PROP} !_ _ / : assert.

Section Ofe_Cofe.
Context {I : biIndex} {PROP : bi}.
#[local] Notation monPred := (monPred I PROP).
Implicit Types i : I.
Implicit Types P Q : monPred.

(** Ofe + Cofe instances  *)

  Inductive monPred_equiv' P Q : Prop :=
    { monPred_in_equiv i : P i ≡ Q i } .
  #[local] Instance monPred_equiv : Equiv monPred := monPred_equiv'.
  Inductive monPred_dist' (n : nat) (P Q : monPred) : Prop :=
    { monPred_in_dist i : P i ≡{n}≡ Q i }.
  #[local] Instance monPred_dist : Dist monPred := monPred_dist'.

  (* These two lemma use the wrong Equiv and Dist instance for
    monPred. so we make sure they are not accessible outside of the
    section by using Let. *)
  Let monPred_sig_equiv P Q : P ≡ Q ↔ monPred_at P ≡@{I-d>PROP} monPred_at Q.
  Proof. by split; [intros []|]. Qed.
  Let monPred_sig_dist n (P Q : monPred) : P ≡{n}≡ Q ↔ monPred_at P ≡{n}@{I-d>PROP}≡ monPred_at Q.
  Proof. by split; [intros []|]. Qed.

  Definition monPred_ofe_mixin : OfeMixin monPred.
  Proof. apply (iso_ofe_mixin (A:=I-d>PROP) monPred_at monPred_sig_equiv monPred_sig_dist). Qed.

  Canonical Structure monPredO := OfeT monPred monPred_ofe_mixin.

  Global Instance monPred_cofe `{Cofe PROP} : Cofe monPredO.
  Proof. exact: (iso_cofe (A:=I-d>PROP) MonPred monPred_at). Qed.

(* We generalize over the relation R which is morally the equivalence
   relation over B. That way, the BI index can use equality as an
   equivalence relation (and Coq is able to infer the Proper and
   Reflexive instances properly), or any other equivalence relation,
   provided it is compatible with (⊑). *)
Global Instance monPred_at_ne :
  ∀ n, Proper (dist n ==> (=) ==> dist n) monPred_at.
Proof. by intros ??? [Hd] ?? ->. Qed.
Global Instance monPred_at_proper (R : relation I) :
  Proper ((≡) ==> (=) ==> (≡)) monPred_at.
Proof. repeat intro. subst. apply equiv_dist=>?. f_equiv => //. by apply equiv_dist. Qed.
End Ofe_Cofe.

Global Arguments monPredO _ _ : clear implicits.

Section Bi.
Context {I : biIndex} {PROP : bi}.
Implicit Types i : I.
Notation monPred := (monPred I PROP).
Implicit Types P Q : monPred.

Definition monPred_entails (P1 P2 : monPred) : Prop :=
  ∀ i , P1 i ⊢ P2 i.
(* #[local] Hint Immediate monPred_in_entails : core. *)

Definition monPred_embed_def : Embed PROP monPred := λ (P : PROP), MonPred (λ _, P).
Definition monPred_embed_aux : seal (@monPred_embed_def). Proof. by eexists. Qed.
Definition monPred_embed := monPred_embed_aux.(unseal).
Definition monPred_embed_eq : @embed _ _ monPred_embed = _ := monPred_embed_aux.(seal_eq).

Definition monPred_emp_def : monPred := MonPred (λ _, emp)%I.
Definition monPred_emp_aux : seal (@monPred_emp_def). Proof. by eexists. Qed.
Definition monPred_emp := monPred_emp_aux.(unseal).
Definition monPred_emp_eq : @monPred_emp = _ := monPred_emp_aux.(seal_eq).

Definition monPred_pure_def (φ : Prop) : monPred := MonPred (λ _, ⌜φ⌝)%I.
Definition monPred_pure_aux : seal (@monPred_pure_def). Proof. by eexists. Qed.
Definition monPred_pure := monPred_pure_aux.(unseal).
Definition monPred_pure_eq : @monPred_pure = _ := monPred_pure_aux.(seal_eq).

Definition monPred_objectively_def P : monPred := MonPred (λ _, ∀ i, P i)%I.
Definition monPred_objectively_aux : seal (@monPred_objectively_def). Proof. by eexists. Qed.
Definition monPred_objectively := monPred_objectively_aux.(unseal).
Definition monPred_objectively_eq : @monPred_objectively = _ := monPred_objectively_aux.(seal_eq).

Definition monPred_subjectively_def P : monPred := MonPred (λ _, ∃ i, P i)%I.
Definition monPred_subjectively_aux : seal (@monPred_subjectively_def). Proof. by eexists. Qed.
Definition monPred_subjectively := monPred_subjectively_aux.(unseal).
Definition monPred_subjectively_eq : @monPred_subjectively = _ := monPred_subjectively_aux.(seal_eq).

Definition monPred_and_def P Q : monPred :=
  MonPred (λ i, P i ∧ Q i)%I.
Definition monPred_and_aux : seal (@monPred_and_def). Proof. by eexists. Qed.
Definition monPred_and := monPred_and_aux.(unseal).
Definition monPred_and_eq : @monPred_and = _ := monPred_and_aux.(seal_eq).

Definition monPred_or_def P Q : monPred :=
  MonPred (λ i, P i ∨ Q i)%I.
Definition monPred_or_aux : seal (@monPred_or_def). Proof. by eexists. Qed.
Definition monPred_or := monPred_or_aux.(unseal).
Definition monPred_or_eq : @monPred_or = _ := monPred_or_aux.(seal_eq).

Definition monPred_impl_def P Q : monPred := MonPred (λ i, P i → Q i)%I.
Definition monPred_impl_aux : seal (@monPred_impl_def). Proof. by eexists. Qed.
Definition monPred_impl := monPred_impl_aux.(unseal).
Definition monPred_impl_eq : @monPred_impl = _ := monPred_impl_aux.(seal_eq).

Definition monPred_forall_def A (Φ : A → monPred) : monPred :=
  MonPred (λ i, ∀ x : A, Φ x i)%I.
Definition monPred_forall_aux : seal (@monPred_forall_def). Proof. by eexists. Qed.
Definition monPred_forall := monPred_forall_aux.(unseal).
Definition monPred_forall_eq : @monPred_forall = _ := monPred_forall_aux.(seal_eq).

Definition monPred_exist_def A (Φ : A → monPred) : monPred :=
  MonPred (λ i, ∃ x : A, Φ x i)%I.
Definition monPred_exist_aux : seal (@monPred_exist_def). Proof. by eexists. Qed.
Definition monPred_exist := monPred_exist_aux.(unseal).
Definition monPred_exist_eq : @monPred_exist = _ := monPred_exist_aux.(seal_eq).

Definition monPred_sep_def P Q : monPred :=
  MonPred (λ i, P i ∗ Q i)%I.
Definition monPred_sep_aux : seal (@monPred_sep_def). Proof. by eexists. Qed.
Definition monPred_sep := monPred_sep_aux.(unseal).
Definition monPred_sep_eq : @monPred_sep = _ := monPred_sep_aux.(seal_eq).

Definition monPred_wand_def P Q : monPred :=
  MonPred (λ i, P i -∗ Q i)%I. (* PG: No upclosure needed. *)
Definition monPred_wand_aux : seal (@monPred_wand_def). Proof. by eexists. Qed.
Definition monPred_wand := monPred_wand_aux.(unseal).
Definition monPred_wand_eq : @monPred_wand = _ := monPred_wand_aux.(seal_eq).

Definition monPred_persistently_def P : monPred :=
  MonPred (λ i, <pers> (P i))%I. (* PG: No upclosure needed. *)
Definition monPred_persistently_aux : seal (@monPred_persistently_def). Proof. by eexists. Qed.
Definition monPred_persistently := monPred_persistently_aux.(unseal).
Definition monPred_persistently_eq : @monPred_persistently = _ := monPred_persistently_aux.(seal_eq).

Definition monPred_in_def (i0 : I) : monPred :=
  MonPred (λ i : I, <affine> ⌜i0 = i⌝)%I. (* PG: Added affinity over Iris. *)
Definition monPred_in_aux : seal (@monPred_in_def). Proof. by eexists. Qed.
Definition monPred_in := monPred_in_aux.(unseal).
Definition monPred_in_eq : @monPred_in = _ := monPred_in_aux.(seal_eq).

Definition monPred_later_def P : monPred := MonPred (λ i, ▷ (P i))%I.
Definition monPred_later_aux : seal monPred_later_def. Proof. by eexists. Qed.
Definition monPred_later := monPred_later_aux.(unseal).
Definition monPred_later_eq : monPred_later = _ := monPred_later_aux.(seal_eq).
End Bi.

Module Import MonPred.
Definition unseal_eqs :=
  (@monPred_and_eq, @monPred_or_eq, @monPred_impl_eq,
   @monPred_forall_eq, @monPred_exist_eq, @monPred_sep_eq, @monPred_wand_eq,
   @monPred_persistently_eq, @monPred_later_eq, @monPred_in_eq,
   @monPred_embed_eq, @monPred_emp_eq, @monPred_pure_eq,
   @monPred_objectively_eq, @monPred_subjectively_eq).
Ltac unseal :=
  unfold bi_affinely, bi_absorbingly, bi_except_0, bi_pure, bi_emp,
         bi_and, bi_or,
         bi_impl, bi_forall, bi_exist, bi_sep, bi_wand,
         bi_persistently, bi_affinely, bi_later;
  simpl;
  rewrite !unseal_eqs /=.
End MonPred.

Section canonical.
Context (I : biIndex) (PROP : bi).

Lemma monPred_bi_mixin : BiMixin (PROP:=monPred I PROP)
  monPred_entails monPred_emp monPred_pure monPred_and monPred_or
  monPred_impl monPred_forall monPred_exist monPred_sep monPred_wand
  monPred_persistently.
Proof.
  split; try unseal; try by (split=> ? /=; repeat f_equiv).
  all: rewrite /monPred_entails/=.
  - split.
    + intros P. by [].
    + intros P Q R H1 H2 ?. by rewrite H1 H2.
  - split.
    + intros [HPQ]. split => i; move: (HPQ i); by apply bi.equiv_spec.
    + intros []. split=>i. by apply bi.equiv_spec.
  - intros P φ ? i. by apply bi.pure_intro.
  - intros φ P HP i. apply bi.pure_elim'=> ?. by apply HP.
  - intros P Q i. by apply bi.and_elim_l.
  - intros P Q i. by apply bi.and_elim_r.
  - intros P Q R ? ? i. by apply bi.and_intro.
  - intros P Q i. by apply bi.or_intro_l.
  - intros P Q i. by apply bi.or_intro_r.
  - intros P Q R ?? i. by apply bi.or_elim.
  - intros P Q R HR i. apply bi.impl_intro_r, HR.
  - intros P Q R HR i. rewrite HR. apply bi.impl_elim_l.
  - intros A P Ψ HΨ i. apply bi.forall_intro => ?. by apply HΨ.
  - intros A Ψ a i. by apply: bi.forall_elim.
  - intros A Ψ a i. by rewrite /= -bi.exist_intro.
  - intros A Ψ Q HΨ i. apply bi.exist_elim => a. by apply HΨ.
  - intros P P' Q Q' ?? i. by apply bi.sep_mono.
  - intros P i. by apply bi.emp_sep_1.
  - intros P i. by apply bi.emp_sep_2.
  - intros P Q i. by apply bi.sep_comm'.
  - intros P Q R i. by apply bi.sep_assoc'.
  - intros P Q R HR i. apply bi.wand_intro_r, HR.
  - intros P Q R HR i.
    rewrite HR. apply bi.wand_elim_l.
  - intros P Q ? i. by f_equiv.
  - intros P i. by apply bi.persistently_idemp_2.
  - intros i. by apply bi.persistently_emp_intro.
  - intros A Ψ i. by apply bi.persistently_forall_2.
  - intros A Ψ i. by apply bi.persistently_exist_1.
  - intros P Q i. apply: bi.sep_elim_l.
  - intros P Q i. by apply bi.persistently_and_sep_elim.
Qed.
