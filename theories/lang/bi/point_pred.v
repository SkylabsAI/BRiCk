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

(* A simplification of monPred that assumes equality on the argument and doesn't seal. *)

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

Section Ofe_Cofe_def.
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
End Ofe_Cofe_def.

  Global Instance monPred_at_ne :
    ∀ n, Proper (dist n ==> (=) ==> dist n) monPred_at.
  Proof. by intros ??? [Hd] ?? ->. Qed.
  Global Instance monPred_at_proper :
    Proper ((≡) ==> (=) ==> (≡)) monPred_at.
  Proof. repeat intro. subst. apply equiv_dist=>?. f_equiv => //. by apply equiv_dist. Qed.

Definition monPred_to (f : I -d> PROP) : monPredO := MonPred f.
Definition monPred_from (f : monPredO) : I -d> PROP := monPred_at f.

#[global] Instance monPred_to_ne : NonExpansive monPred_to.
Proof. intros ????. by split => ?. Qed.
#[global] Instance monPred_to_proper : Proper ((≡) ==> (≡)) monPred_to.
Proof. apply: ne_proper. Qed.

#[global] Instance monPred_from_ne : NonExpansive monPred_from.
Proof. solve_proper. Qed.
#[global] Instance monPred_from_proper : Proper ((≡) ==> (≡)) monPred_from.
Proof. apply: ne_proper. Qed.

Lemma monPred_from_to (P' : I -d> PROP) : monPred_from (monPred_to P') ≡ P'.
Proof. done. Qed.
Lemma monPred_to_from P : monPred_to (monPred_from P) ≡ P.
Proof. done. Qed.

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

Definition monPred_embed : Embed PROP monPred := λ (P : PROP), MonPred (λ _, P).

Definition monPred_emp : monPred := MonPred (λ _, emp)%I.

Definition monPred_pure (φ : Prop) : monPred := MonPred (λ _, ⌜φ⌝)%I.

Definition monPred_objectively_def P : monPred := MonPred (λ _, ∀ i, P i)%I.
Definition monPred_objectively_aux : seal (@monPred_objectively_def). Proof. by eexists. Qed.
Definition monPred_objectively := monPred_objectively_aux.(unseal).
Definition monPred_objectively_eq : @monPred_objectively = _ := monPred_objectively_aux.(seal_eq).

Definition monPred_subjectively_def P : monPred := MonPred (λ _, ∃ i, P i)%I.
Definition monPred_subjectively_aux : seal (@monPred_subjectively_def). Proof. by eexists. Qed.
Definition monPred_subjectively := monPred_subjectively_aux.(unseal).
Definition monPred_subjectively_eq : @monPred_subjectively = _ := monPred_subjectively_aux.(seal_eq).

Definition monPred_and P Q : monPred :=
  MonPred (λ i, P i ∧ Q i)%I.

Definition monPred_or P Q : monPred :=
  MonPred (λ i, P i ∨ Q i)%I.

Definition monPred_impl P Q : monPred := MonPred (λ i, P i → Q i)%I.

Definition monPred_forall A (Φ : A → monPred) : monPred :=
  MonPred (λ i, ∀ x : A, Φ x i)%I.

Definition monPred_exist A (Φ : A → monPred) : monPred :=
  MonPred (λ i, ∃ x : A, Φ x i)%I.

Definition monPred_sep P Q : monPred :=
  MonPred (λ i, P i ∗ Q i)%I.

Definition monPred_wand P Q : monPred :=
  MonPred (λ i, P i -∗ Q i)%I. (* PG: No upclosure needed. *)

Definition monPred_persistently P : monPred :=
  MonPred (λ i, <pers> (P i))%I. (* PG: No upclosure needed. *)

Definition monPred_in (i0 : I) : monPred :=
  MonPred (λ i : I, <affine> ⌜i0 = i⌝)%I. (* PG: Added affinity over Iris. *)

Definition monPred_later P : monPred := MonPred (λ i, ▷ (P i))%I.
End Bi.

Global Arguments monPred_objectively {_ _} _%I.
Global Arguments monPred_subjectively {_ _} _%I.
Notation "'<obj>' P" := (monPred_objectively P) : bi_scope.
Notation "'<subj>' P" := (monPred_subjectively P) : bi_scope.

Module Import MonPred.
(* "unseal folding". TODO name. *)
Ltac unsealf :=
  unfold bi_affinely, bi_absorbingly, bi_except_0, bi_pure, bi_emp,
         bi_and, bi_or,
         bi_impl, bi_forall, bi_exist, bi_sep, bi_wand,
         bi_persistently, bi_affinely, bi_later; simpl.

Definition unseal_eqs :=
  (
    (* @monPred_and_eq, @monPred_or_eq, @monPred_impl_eq,
   @monPred_forall_eq, @monPred_exist_eq, @monPred_sep_eq, @monPred_wand_eq,
   @monPred_persistently_eq, @monPred_later_eq, @monPred_in_eq,
   @monPred_embed_eq, @monPred_emp_eq, @monPred_pure_eq, *)
   @monPred_objectively_eq, @monPred_subjectively_eq).
Ltac unseal := unsealf; rewrite ?unseal_eqs /=.
End MonPred.

Section canonical.
Context (I : biIndex) (PROP : bi).

Lemma monPred_bi_mixin : BiMixin (PROP:=monPred I PROP)
  monPred_entails monPred_emp monPred_pure monPred_and monPred_or
  monPred_impl monPred_forall monPred_exist monPred_sep monPred_wand
  monPred_persistently.
Proof.
  split; try by (split=> ? /=; repeat f_equiv).
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

Lemma monPred_bi_later_mixin :
  BiLaterMixin (PROP:=monPred I PROP) monPred_entails monPred_pure
               monPred_or monPred_impl monPred_forall monPred_exist
               monPred_sep monPred_persistently monPred_later.
Proof.
  split; unseal.
  all: rewrite /monPred_entails/=.
  - by split=> ? /=; repeat f_equiv.
  - intros P Q ? i. by apply bi.later_mono.
  - intros P i. by apply bi.later_intro.
  - intros A Ψ i. by apply bi.later_forall_2.
  - intros A Ψ i. by apply bi.later_exist_false.
  - intros P Q i. by apply bi.later_sep_1.
  - intros P Q i. by apply bi.later_sep_2.
  - intros P i. by apply bi.later_persistently_1.
  - intros P i. by apply bi.later_persistently_2.
  - intros P i. apply bi.later_false_em.
Qed.

Canonical Structure monPredI : bi :=
  {| bi_ofe_mixin := monPred_ofe_mixin; bi_bi_mixin := monPred_bi_mixin;
     bi_bi_later_mixin := monPred_bi_later_mixin |}.
End canonical.

Class Objective {I : biIndex} {PROP : bi} (P : monPred I PROP) :=
  objective_at i j : P i -∗ P j.
Global Arguments Objective {_ _} _%I.
Global Arguments objective_at {_ _} _%I {_}.
Global Hint Mode Objective + + ! : typeclass_instances.
Global Instance: Params (@Objective) 2 := {}.

Section bi_facts.
Context {I : biIndex} {PROP : bi}.
Local Notation monPred := (monPred I PROP).
Local Notation monPredI := (monPredI I PROP).
Local Notation monPred_at := (@monPred_at I PROP).
Implicit Types i : I.
Implicit Types P Q : monPred.

(** monPred_at unfolding laws *)

Lemma monPred_at_pure i (φ : Prop) : monPred_at ⌜φ⌝ i ⊣⊢ ⌜φ⌝.
Proof.
  (* Demonstrate simplification problem. *)
  unsealf. (* This works, but unfolds the bi structure by hand. *)
  Show.

  Undo.
  (* But I don't see anything else that works. *)


  cbn.
  Show.
  simpl.
  Show.
  #[global] Arguments point_pred.monPred_at {I} {PROP} _ _ / : assert.
  simpl.
  Show.
  unsealf.
  Show.
  done.
Qed.
(* XXX Restore old setting *)
#[global] Arguments point_pred.monPred_at {I} {PROP} !_ _ / : assert.

Lemma monPred_at_emp i : monPred_at emp i ⊣⊢ emp.
Proof. by unseal. Qed.
Lemma monPred_at_and i P Q : (P ∧ Q) i ⊣⊢ P i ∧ Q i.
Proof. by unseal. Qed.
Lemma monPred_at_or i P Q : (P ∨ Q) i ⊣⊢ P i ∨ Q i.
Proof. by unseal. Qed.
Lemma monPred_at_impl i P Q : (P → Q) i ⊣⊢ (P i → Q i).
Proof. by unseal. Qed.
Lemma monPred_at_forall {A} i (Φ : A → monPred) : (∀ x, Φ x) i ⊣⊢ ∀ x, Φ x i.
Proof. by unseal. Qed.
Lemma monPred_at_exist {A} i (Φ : A → monPred) : (∃ x, Φ x) i ⊣⊢ ∃ x, Φ x i.
Proof. by unseal. Qed.
Lemma monPred_at_sep i P Q : (P ∗ Q) i ⊣⊢ P i ∗ Q i.
Proof. by unseal. Qed.
Lemma monPred_at_wand i P Q : (P -∗ Q) i ⊣⊢ (P i -∗ Q i).
Proof. by unseal. Qed.
Lemma monPred_at_persistently i P : (<pers> P) i ⊣⊢ <pers> (P i).
Proof. by unseal. Qed.
Lemma monPred_at_in i j : monPred_at (monPred_in j) i ⊣⊢ <affine> ⌜j = i⌝.
Proof. by unseal. Qed.
Lemma monPred_at_objectively i P : (<obj> P) i ⊣⊢ ∀ j, P j.
Proof. by unseal. Qed.
Lemma monPred_at_subjectively i P : (<subj> P) i ⊣⊢ ∃ j, P j.
Proof. by unseal. Qed.
Lemma monPred_at_persistently_if i p P : (<pers>?p P) i ⊣⊢ <pers>?p (P i).
Proof. destruct p=>//=. Qed.
Lemma monPred_at_affinely i P : (<affine> P) i ⊣⊢ <affine> (P i).
Proof. by rewrite /bi_affinely monPred_at_and monPred_at_emp. Qed.
Lemma monPred_at_affinely_if i p P : (<affine>?p P) i ⊣⊢ <affine>?p (P i).
Proof. destruct p=>//=.  Qed.
Lemma monPred_at_intuitionistically i P : (□ P) i ⊣⊢ □ (P i).
Proof. by rewrite /bi_intuitionistically monPred_at_affinely monPred_at_persistently. Qed.
Lemma monPred_at_intuitionistically_if i p P : (□?p P) i ⊣⊢ □?p (P i).
Proof. destruct p=>//=.  Qed.

Lemma monPred_at_absorbingly i P : (<absorb> P) i ⊣⊢ <absorb> (P i).
Proof. by rewrite /bi_absorbingly monPred_at_sep monPred_at_pure. Qed.
Lemma monPred_at_absorbingly_if i p P : (<absorb>?p P) i ⊣⊢ <absorb>?p (P i).
Proof. destruct p=>//=.  Qed.

(* PG: updated. *)
Lemma monPred_wand_force i P Q : (P -∗ Q) i ⊣⊢ (P i -∗ Q i).
Proof. exact: monPred_at_wand. Qed.
Lemma monPred_impl_force i P Q : (P → Q) i ⊣⊢ (P i → Q i).
Proof. exact: monPred_at_impl. Qed.

(** Instances *)
Global Instance monPred_at_mono :
  Proper ((⊢) ==> (=) ==> (⊢)) monPred_at.
Proof. by move=> ?? ? ?? ->. Qed.
Global Instance monPred_at_flip_mono :
  Proper (flip (⊢) ==> (=) ==> flip (⊢)) monPred_at.
Proof. solve_proper. Qed.

Global Instance monPred_in_proper :
  Proper ((=) ==> (≡)) (@monPred_in I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance monPred_in_mono : Proper ((=) ==> (⊢)) (@monPred_in I PROP).
Proof. unseal. solve_proper. Qed.
Global Instance monPred_in_flip_mono : Proper ((=) ==> flip (⊢)) (@monPred_in I PROP).
Proof. solve_proper. Qed.

Global Instance monPred_pure_forall : BiPureForall PROP → BiPureForall monPredI.
Proof. intros ? A φ i. unseal. by apply pure_forall_2. Qed.

Global Instance monPred_later_contractive :
  BiLaterContractive PROP → BiLaterContractive monPredI.
Proof. unseal=> ? n P Q HPQ. split=> i /=. f_contractive. apply HPQ. Qed.
Global Instance monPred_bi_löb : BiLöb PROP → BiLöb monPredI.
Proof. rewrite {2}/BiLöb; unseal=> ? P HP i /=. apply löb_weak, HP. Qed.
Global Instance monPred_bi_positive : BiPositive PROP → BiPositive monPredI.
Proof. intros ????. unseal. apply bi_positive. Qed.
Global Instance monPred_bi_affine : BiAffine PROP → BiAffine monPredI.
Proof. intros ???. unseal. by apply affine. Qed.

Lemma monPred_persistent P : (∀ i, Persistent (P i)) → Persistent P.
Proof. intros HP i. unseal. apply HP. Qed.
Lemma monPred_absorbing P : (∀ i, Absorbing (P i)) → Absorbing P.
Proof. intros HP i. unseal. apply HP. Qed.
Lemma monPred_affine P : (∀ i, Affine (P i)) → Affine P.
Proof. intros HP i. unseal. apply HP. Qed.

Global Instance monPred_at_persistent P i : Persistent P → Persistent (P i).
Proof. move => /(_ i). by unseal. Qed.
Global Instance monPred_at_absorbing P i : Absorbing P → Absorbing (P i).
Proof. move => /(_ i). unfold Absorbing. by unseal. Qed.
Global Instance monPred_at_affine P i : Affine P → Affine (P i).
Proof. move => /(_ i). unfold Affine. by unseal. Qed.

(** Note that [monPred_in] is *not* [Plain], because it depends on the index. *)
Global Instance monPred_in_persistent i : Persistent (@monPred_in I PROP i).
Proof. apply monPred_persistent=> j. rewrite monPred_at_in. apply _. Qed.
Global Instance monPred_in_affine i : Affine (@monPred_in I PROP i). (* PG: was [Absorbing] *)
Proof. apply monPred_affine=> j. rewrite monPred_at_in. apply _. Qed.

Definition monPred_embedding_mixin : BiEmbedMixin PROP monPredI monPred_embed.
Proof.
  split; try apply _; rewrite /bi_emp_valid; unseal; try done.
  - by repeat intro.
  - move=> P /= /(_ inhabitant) ? //.
  - intros PROP' ? P Q.
    set (f P := monPred_at P inhabitant).
    assert (NonExpansive f) by solve_proper.
    apply (f_equivI f).
Qed.
Global Instance monPred_bi_embed : BiEmbed PROP monPredI :=
  {| bi_embed_mixin := monPred_embedding_mixin |}.
Global Instance monPred_bi_embed_emp : BiEmbedEmp PROP monPredI.
Proof. intro. by unseal. Qed.

Lemma monPred_at_embed i (P : PROP) : monPred_at ⎡P⎤ i ⊣⊢ P.
Proof. by unseal. Qed.

Lemma monPred_emp_unfold : emp%I = ⎡emp : PROP⎤%I.
Proof. by unseal. Qed.
Lemma monPred_pure_unfold : bi_pure = λ φ, ⎡ ⌜ φ ⌝ : PROP⎤%I.
Proof. by unseal. Qed.
Lemma monPred_objectively_unfold : monPred_objectively = λ P, ⎡∀ i, P i⎤%I.
Proof. by unseal. Qed.
Lemma monPred_subjectively_unfold : monPred_subjectively = λ P, ⎡∃ i, P i⎤%I.
Proof. by unseal. Qed.

Global Instance monPred_objectively_ne : NonExpansive (@monPred_objectively I PROP).
Proof. rewrite monPred_objectively_unfold. solve_proper. Qed.
Global Instance monPred_objectively_proper : Proper ((≡) ==> (≡)) (@monPred_objectively I PROP).
Proof. apply (ne_proper _). Qed.
Lemma monPred_objectively_mono P Q : (P ⊢ Q) → (<obj> P ⊢ <obj> Q).
Proof. rewrite monPred_objectively_unfold. solve_proper. Qed.
Global Instance monPred_objectively_mono' : Proper ((⊢) ==> (⊢)) (@monPred_objectively I PROP).
Proof. intros ???. by apply monPred_objectively_mono. Qed.
Global Instance monPred_objectively_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_objectively I PROP).
Proof. intros ???. by apply monPred_objectively_mono. Qed.

Global Instance monPred_objectively_persistent P : Persistent P → Persistent (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.
Global Instance monPred_objectively_absorbing P : Absorbing P → Absorbing (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.
Global Instance monPred_objectively_affine P : Affine P → Affine (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.

Global Instance monPred_subjectively_ne : NonExpansive (@monPred_subjectively I PROP).
Proof. rewrite monPred_subjectively_unfold. solve_proper. Qed.
Global Instance monPred_subjectively_proper : Proper ((≡) ==> (≡)) (@monPred_subjectively I PROP).
Proof. apply (ne_proper _). Qed.
Lemma monPred_subjectively_mono P Q : (P ⊢ Q) → <subj> P ⊢ <subj> Q.
Proof. rewrite monPred_subjectively_unfold. solve_proper. Qed.
Global Instance monPred_subjectively_mono' : Proper ((⊢) ==> (⊢)) (@monPred_subjectively I PROP).
Proof. intros ???. by apply monPred_subjectively_mono. Qed.
Global Instance monPred_subjectively_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@monPred_subjectively I PROP).
Proof. intros ???. by apply monPred_subjectively_mono. Qed.

Global Instance monPred_subjectively_persistent P : Persistent P → Persistent (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.
Global Instance monPred_subjectively_absorbing P : Absorbing P → Absorbing (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.
Global Instance monPred_subjectively_affine P : Affine P → Affine (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.

(* Laws for monPred_objectively and of Objective. *)
Lemma monPred_objectively_elim P : <obj> P ⊢ P.
Proof. rewrite monPred_objectively_unfold. unseal =>?. apply bi.forall_elim. Qed.
Lemma monPred_objectively_idemp P : <obj> <obj> P ⊣⊢ <obj> P.
Proof.
  apply bi.equiv_spec; split; [by apply monPred_objectively_elim|].
  unseal =>i /=. by apply bi.forall_intro=>_.
Qed.

Lemma monPred_objectively_forall {A} (Φ : A → monPred) : <obj> (∀ x, Φ x) ⊣⊢ ∀ x, <obj> (Φ x).
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=;
    do 2 apply bi.forall_intro=>?; by do 2 rewrite bi.forall_elim.
Qed.
Lemma monPred_objectively_and P Q : <obj> (P ∧ Q) ⊣⊢ <obj> P ∧ <obj> Q.
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=.
  - apply bi.and_intro; do 2 f_equiv.
    + apply bi.and_elim_l.
    + apply bi.and_elim_r.
  - apply bi.forall_intro=>?. by rewrite !bi.forall_elim.
Qed.
Lemma monPred_objectively_exist {A} (Φ : A → monPred) :
  (∃ x, <obj> (Φ x)) ⊢ <obj> (∃ x, (Φ x)).
Proof. apply bi.exist_elim=>?. f_equiv. apply bi.exist_intro. Qed.
Lemma monPred_objectively_or P Q : <obj> P ∨ <obj> Q ⊢ <obj> (P ∨ Q).
Proof.
  apply bi.or_elim; f_equiv.
  - apply bi.or_intro_l.
  - apply bi.or_intro_r.
Qed.

Lemma monPred_objectively_sep_2 P Q : <obj> P ∗ <obj> Q ⊢ <obj> (P ∗ Q).
Proof. unseal =>i /=. apply bi.forall_intro=>?. by rewrite !bi.forall_elim. Qed.

(* Lemma monPred_objectively_sep_1 P Q : <obj> (P ∗ Q) ⊢ <obj> P ∗ <obj> Q.
Proof. unseal =>i /=.

Require Import iris.proofmode.tactics.
iIntros "H".

apply bi.forall_elim. =>?. by rewrite !bi.forall_elim. Qed.
Lemma monPred_objectively_sep P Q : <obj> (P ∗ Q) ⊣⊢ <obj> P ∗ <obj> Q.
Proof.
  apply bi.equiv_spec, conj, monPred_objectively_sep_2. unseal=>i /=.
  rewrite (bi.forall_elim j). f_equiv; apply bi.forall_intro=>j; f_equiv.
Qed. *)

Lemma monPred_objectively_embed (P : PROP) : <obj> ⎡P⎤ ⊣⊢ ⎡P⎤.
Proof.
  apply bi.equiv_spec; split; unseal =>i /=.
  - by rewrite (bi.forall_elim inhabitant).
  - by apply bi.forall_intro.
Qed.
Lemma monPred_objectively_emp : <obj> (emp : monPred) ⊣⊢ emp.
Proof. rewrite monPred_emp_unfold. apply monPred_objectively_embed. Qed.
Lemma monPred_objectively_pure φ : <obj> (⌜ φ ⌝ : monPred) ⊣⊢ ⌜ φ ⌝.
Proof. rewrite monPred_pure_unfold. apply monPred_objectively_embed. Qed.

Lemma monPred_subjectively_intro P : P ⊢ <subj> P.
Proof. unseal =>?. apply bi.exist_intro. Qed.

Lemma monPred_subjectively_forall {A} (Φ : A → monPred) :
  (<subj> (∀ x, Φ x)) ⊢ ∀ x, <subj> (Φ x).
Proof. apply bi.forall_intro=>?. f_equiv. apply bi.forall_elim. Qed.
Lemma monPred_subjectively_and P Q : <subj> (P ∧ Q) ⊢ <subj> P ∧ <subj> Q.
Proof.
  apply bi.and_intro; f_equiv.
  - apply bi.and_elim_l.
  - apply bi.and_elim_r.
Qed.
Lemma monPred_subjectively_exist {A} (Φ : A → monPred) : <subj> (∃ x, Φ x) ⊣⊢ ∃ x, <subj> (Φ x).
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=;
    do 2 apply bi.exist_elim=>?; by do 2 rewrite -bi.exist_intro.
Qed.
Lemma monPred_subjectively_or P Q : <subj> (P ∨ Q) ⊣⊢ <subj> P ∨ <subj> Q.
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=.
  - apply bi.exist_elim=>?. by rewrite -!bi.exist_intro.
  - apply bi.or_elim; do 2 f_equiv.
    + apply bi.or_intro_l.
    + apply bi.or_intro_r.
Qed.

Lemma monPred_subjectively_sep P Q : <subj> (P ∗ Q) ⊢ <subj> P ∗ <subj> Q.
Proof. unseal=>i /=. apply bi.exist_elim=>?. by rewrite -!bi.exist_intro. Qed.

Lemma monPred_subjectively_idemp P : <subj> <subj> P ⊣⊢ <subj> P.
Proof.
  apply bi.equiv_spec; split; [|by apply monPred_subjectively_intro].
  unseal =>i /=. by apply bi.exist_elim=>_.
Qed.

Lemma objective_objectively P `{!Objective P} : P ⊢ <obj> P.
Proof.
  rewrite monPred_objectively_unfold /= embed_forall. apply bi.forall_intro=>??.
  unseal. apply objective_at, _.
Qed.
Lemma objective_subjectively P `{!Objective P} : <subj> P ⊢ P.
Proof.
  rewrite monPred_subjectively_unfold /= embed_exist. apply bi.exist_elim=>??.
  unseal. apply objective_at, _.
Qed.

Global Instance embed_objective (P : PROP) : @Objective I PROP ⎡P⎤.
Proof. intros ??. by unseal. Qed.
Global Instance pure_objective φ : @Objective I PROP ⌜φ⌝.
Proof. intros ??. by unseal. Qed.
Global Instance emp_objective : @Objective I PROP emp.
Proof. intros ??. by unseal. Qed.
Global Instance objectively_objective P : Objective (<obj> P).
Proof. intros ??. by unseal. Qed.
Global Instance subjectively_objective P : Objective (<subj> P).
Proof. intros ??. by unseal. Qed.

Global Instance and_objective P Q `{!Objective P, !Objective Q} : Objective (P ∧ Q).
Proof. intros i j. unseal. by rewrite !(objective_at _ i j). Qed.
Global Instance or_objective P Q `{!Objective P, !Objective Q} : Objective (P ∨ Q).
Proof. intros i j. by rewrite !monPred_at_or !(objective_at _ i j). Qed.
Global Instance impl_objective P Q `{!Objective P, !Objective Q} : Objective (P → Q).
Proof. intros i j. unseal. by rewrite (objective_at Q i) (objective_at P j). Qed.
Global Instance forall_objective {A} Φ {H : ∀ x : A, Objective (Φ x)} :
  @Objective I PROP (∀ x, Φ x)%I.
Proof. intros i j. unseal. do 2 f_equiv. by apply objective_at. Qed.
Global Instance exists_objective {A} Φ {H : ∀ x : A, Objective (Φ x)} :
  @Objective I PROP (∃ x, Φ x)%I.
Proof. intros i j. unseal. do 2 f_equiv. by apply objective_at. Qed.

Global Instance sep_objective P Q `{!Objective P, !Objective Q} : Objective (P ∗ Q).
Proof. intros i j. unseal. by rewrite !(objective_at _ i j). Qed.
Global Instance wand_objective P Q `{!Objective P, !Objective Q} : Objective (P -∗ Q).
Proof. intros i j. unseal. by rewrite (objective_at Q i) (objective_at P j). Qed.
Global Instance persistently_objective P `{!Objective P} : Objective (<pers> P).
Proof. intros i j. unseal. by rewrite objective_at. Qed.

Global Instance affinely_objective P `{!Objective P} : Objective (<affine> P).
Proof. rewrite /bi_affinely. apply _. Qed.
Global Instance intuitionistically_objective P `{!Objective P} : Objective (□ P).
Proof. rewrite /bi_intuitionistically. apply _. Qed.
Global Instance absorbingly_objective P `{!Objective P} : Objective (<absorb> P).
Proof. rewrite /bi_absorbingly. apply _. Qed.
Global Instance persistently_if_objective P p `{!Objective P} : Objective (<pers>?p P).
Proof. rewrite /bi_persistently_if. destruct p; apply _. Qed.
Global Instance affinely_if_objective P p `{!Objective P} : Objective (<affine>?p P).
Proof. rewrite /bi_affinely_if. destruct p; apply _. Qed.
Global Instance absorbingly_if_objective P p `{!Objective P} : Objective (<absorb>?p P).
Proof. rewrite /bi_absorbingly_if. destruct p; apply _. Qed.
Global Instance intuitionistically_if_objective P p `{!Objective P} : Objective (□?p P).
Proof. rewrite /bi_intuitionistically_if. destruct p; apply _. Qed.

(** monPred_in *)
Lemma monPred_in_intro P : P ⊢ ∃ i, monPred_in i ∗ ⎡P i⎤.
Proof.
  unseal=>i /=.
  rewrite -(bi.exist_intro i). apply bi.sep_intro_emp_valid_l => //.
  by apply /bi.affinely_intro /bi.pure_intro.
Qed.
Lemma monPred_in_elim P i : monPred_in i -∗ ⎡P i⎤ → P .
Proof.
  apply bi.impl_intro_r. unseal =>i' /=.
  rewrite bi.affinely_elim.
  eapply bi.pure_elim; [apply bi.and_elim_l|]=>->. apply bi.and_elim_r.
Qed.

(** Big op *)
Global Instance monPred_at_monoid_and_homomorphism i :
  MonoidHomomorphism bi_and bi_and (≡) (flip monPred_at i).
Proof. split; [split|]; try apply _; [apply monPred_at_and | apply monPred_at_pure]. Qed.
Global Instance monPred_at_monoid_or_homomorphism i :
  MonoidHomomorphism bi_or bi_or (≡) (flip monPred_at i).
Proof. split; [split|]; try apply _; [apply monPred_at_or | apply monPred_at_pure]. Qed.
Global Instance monPred_at_monoid_sep_homomorphism i :
  MonoidHomomorphism bi_sep bi_sep (≡) (flip monPred_at i).
Proof. split; [split|]; try apply _; [apply monPred_at_sep | apply monPred_at_emp]. Qed.

Lemma monPred_at_big_sepL {A} i (Φ : nat → A → monPred) l :
  ([∗ list] k↦x ∈ l, Φ k x) i ⊣⊢ [∗ list] k↦x ∈ l, Φ k x i.
Proof. apply (big_opL_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepM `{Countable K} {A} i (Φ : K → A → monPred) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, Φ k x) i ⊣⊢ [∗ map] k↦x ∈ m, Φ k x i.
Proof. apply (big_opM_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepS `{Countable A} i (Φ : A → monPred) (X : gset A) :
  ([∗ set] y ∈ X, Φ y) i ⊣⊢ [∗ set] y ∈ X, Φ y i.
Proof. apply (big_opS_commute (flip monPred_at i)). Qed.
Lemma monPred_at_big_sepMS `{Countable A} i (Φ : A → monPred) (X : gmultiset A) :
  ([∗ mset] y ∈ X, Φ y) i ⊣⊢ ([∗ mset] y ∈ X, Φ y i).
Proof. apply (big_opMS_commute (flip monPred_at i)). Qed.

Global Instance monPred_objectively_monoid_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@monPred_objectively I PROP).
Proof.
  split; [split|]; try apply _.
  - apply monPred_objectively_and.
  - apply monPred_objectively_pure.
Qed.
Global Instance monPred_objectively_monoid_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@monPred_objectively I PROP).
Proof.
  split; [split|]; try apply _.
  - apply monPred_objectively_sep_2.
  - by rewrite monPred_objectively_emp.
Qed.
(* Global Instance monPred_objectively_monoid_sep_homomorphism `{BiIndexBottom bot} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@monPred_objectively I PROP).
Proof.
  split; [split|]; try apply _.
  - apply monPred_objectively_sep.
  - by rewrite monPred_objectively_emp.
Qed. *)

Lemma monPred_objectively_big_sepL_entails {A} (Φ : nat → A → monPred) l :
  ([∗ list] k↦x ∈ l, <obj> (Φ k x)) ⊢ <obj> ([∗ list] k↦x ∈ l, Φ k x).
Proof. apply (big_opL_commute monPred_objectively (R:=flip (⊢))). Qed.
Lemma monPred_objectively_big_sepM_entails
      `{Countable K} {A} (Φ : K → A → monPred) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, <obj> (Φ k x)) ⊢ <obj> ([∗ map] k↦x ∈ m, Φ k x).
Proof. apply (big_opM_commute monPred_objectively (R:=flip (⊢))). Qed.
Lemma monPred_objectively_big_sepS_entails `{Countable A} (Φ : A → monPred) (X : gset A) :
  ([∗ set] y ∈ X, <obj> (Φ y)) ⊢ <obj> ([∗ set] y ∈ X, Φ y).
Proof. apply (big_opS_commute monPred_objectively (R:=flip (⊢))). Qed.
Lemma monPred_objectively_big_sepMS_entails `{Countable A} (Φ : A → monPred) (X : gmultiset A) :
  ([∗ mset] y ∈ X, <obj> (Φ y)) ⊢ <obj> ([∗ mset] y ∈ X, Φ y).
Proof. apply (big_opMS_commute monPred_objectively (R:=flip (⊢))). Qed.

(* Lemma monPred_objectively_big_sepL `{BiIndexBottom bot} {A} (Φ : nat → A → monPred) l :
  <obj> ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, <obj> (Φ k x)).
Proof. apply (big_opL_commute _). Qed.
Lemma monPred_objectively_big_sepM `{BiIndexBottom bot} `{Countable K} {A}
      (Φ : K → A → monPred) (m : gmap K A) :
  <obj> ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, <obj> (Φ k x)).
Proof. apply (big_opM_commute _). Qed.
Lemma monPred_objectively_big_sepS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → monPred) (X : gset A) :
  <obj> ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, <obj> (Φ y)).
Proof. apply (big_opS_commute _). Qed.
Lemma monPred_objectively_big_sepMS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → monPred) (X : gmultiset A) :
  <obj> ([∗ mset] y ∈ X, Φ y) ⊣⊢  ([∗ mset] y ∈ X, <obj> (Φ y)).
Proof. apply (big_opMS_commute _). Qed. *)

Global Instance big_sepL_objective {A} (l : list A) Φ `{∀ n x, Objective (Φ n x)} :
  @Objective I PROP ([∗ list] n↦x ∈ l, Φ n x)%I.
Proof. generalize dependent Φ. induction l=>/=; apply _. Qed.
Global Instance big_sepM_objective `{Countable K} {A}
       (Φ : K → A → monPred) (m : gmap K A) `{∀ k x, Objective (Φ k x)} :
  Objective ([∗ map] k↦x ∈ m, Φ k x)%I.
Proof. intros ??. rewrite !monPred_at_big_sepM. do 3 f_equiv. by apply objective_at. Qed.
Global Instance big_sepS_objective `{Countable A} (Φ : A → monPred)
       (X : gset A) `{∀ y, Objective (Φ y)} :
  Objective ([∗ set] y ∈ X, Φ y)%I.
Proof. intros ??. rewrite !monPred_at_big_sepS. do 2 f_equiv. by apply objective_at. Qed.
Global Instance big_sepMS_objective `{Countable A} (Φ : A → monPred)
       (X : gmultiset A) `{∀ y, Objective (Φ y)} :
  Objective ([∗ mset] y ∈ X, Φ y)%I.
Proof. intros ??. rewrite !monPred_at_big_sepMS. do 2 f_equiv. by apply objective_at. Qed.

(** BUpd *)
Definition monPred_bupd_def `{BiBUpd PROP} (P : monPred) : monPred :=
  MonPred (λ i, |==> P i)%I.
Definition monPred_bupd_aux : seal (@monPred_bupd_def). Proof. by eexists. Qed.
Definition monPred_bupd := monPred_bupd_aux.(unseal).
Local Arguments monPred_bupd {_}.
Lemma monPred_bupd_eq `{BiBUpd PROP} : @bupd _ monPred_bupd = monPred_bupd_def.
Proof. rewrite -monPred_bupd_aux.(seal_eq) //. Qed.

Lemma monPred_bupd_mixin `{BiBUpd PROP} : BiBUpdMixin monPredI monPred_bupd.
Proof.
  split; rewrite monPred_bupd_eq.
  - split=>/= i. solve_proper.
  - intros P i=>/=. apply bupd_intro.
  - intros P Q HPQ i => /=. by rewrite HPQ.
  - intros P i =>/=. apply bupd_trans.
  - intros P Q i => /=. rewrite !monPred_at_sep /=. apply bupd_frame_r.
Qed.
Global Instance monPred_bi_bupd `{BiBUpd PROP} : BiBUpd monPredI :=
  {| bi_bupd_mixin := monPred_bupd_mixin |}.

Lemma monPred_at_bupd `{BiBUpd PROP} i P : (|==> P) i ⊣⊢ |==> P i.
Proof. by rewrite monPred_bupd_eq. Qed.

Global Instance bupd_objective `{BiBUpd PROP} P `{!Objective P} :
  Objective (|==> P)%I.
Proof. intros ??. by rewrite !monPred_at_bupd objective_at. Qed.

Global Instance monPred_bi_embed_bupd `{BiBUpd PROP} :
  BiEmbedBUpd PROP monPredI.
Proof. split=>i /=. by rewrite monPred_at_bupd !monPred_at_embed. Qed.

(** Later *)
Global Instance monPred_bi_embed_later : BiEmbedLater PROP monPredI.
Proof. split; by unseal. Qed.

Global Instance monPred_at_timeless P i : Timeless P → Timeless (P i).
Proof. move => /(_ i). unfold Timeless. by unseal. Qed.
(* PG: Timeless pulled in by affinely_timeless. *)
Global Instance monPred_in_timeless i0 : Timeless (@bi_emp PROP) -> Timeless (@monPred_in I PROP i0).
Proof. move => ? ? /=. unseal. apply: timeless. Qed.
(* Global Instance monPred_in_timeless i0 : Timeless (@monPred_in I PROP i0).
Proof. move => ? /=. unseal. apply timeless. apply _. Qed. *)
Global Instance monPred_objectively_timeless P : Timeless P → Timeless (<obj> P).
Proof.
  unfold Timeless. unseal=>Hti ? /=.
  by apply timeless, bi.forall_timeless.
Qed.
Global Instance monPred_subjectively_timeless P : Timeless P → Timeless (<subj> P).
Proof.
  unfold Timeless. unseal=>Hti ? /=.
  by apply timeless, bi.exist_timeless.
Qed.

Lemma monPred_at_later i P : (▷ P) i ⊣⊢ ▷ P i.
Proof. by unseal. Qed.
Lemma monPred_at_laterN n i P : (▷^n P) i ⊣⊢ ▷^n P i.
Proof. induction n as [|? IHn]; first done. rewrite /= monPred_at_later IHn //. Qed.
Lemma monPred_at_except_0 i P : (◇ P) i ⊣⊢ ◇ P i.
Proof. by unseal. Qed.

Global Instance later_objective P `{!Objective P} : Objective (▷ P).
Proof. intros ??. unseal. by rewrite objective_at. Qed.
Global Instance laterN_objective P `{!Objective P} n : Objective (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance except0_objective P `{!Objective P} : Objective (◇ P).
Proof. rewrite /bi_except_0. apply _. Qed.

(** Internal equality *)
Definition monPred_internal_eq_def `{!BiInternalEq PROP} (A : ofeT) (a b : A) : monPred :=
  MonPred (λ _, a ≡ b)%I.
Definition monPred_internal_eq_aux : seal (@monPred_internal_eq_def).
Proof. by eexists. Qed.
Definition monPred_internal_eq := monPred_internal_eq_aux.(unseal).
Local Arguments monPred_internal_eq {_}.
Lemma monPred_internal_eq_eq `{!BiInternalEq PROP} :
  @internal_eq _ (@monPred_internal_eq _) = monPred_internal_eq_def.
Proof. rewrite -monPred_internal_eq_aux.(seal_eq) //. Qed.

Lemma monPred_internal_eq_mixin `{!BiInternalEq PROP} :
  BiInternalEqMixin monPredI (@monPred_internal_eq _).
Proof.
  split; rewrite monPred_internal_eq_eq.
  - split=> i /=. solve_proper.
  - intros A P a i =>/=. apply internal_eq_refl.
  - intros A a b Ψ ? => i /=. unseal.
    erewrite (internal_eq_rewrite _ _ (flip Ψ _)) => //=. solve_proper.
  - intros A1 A2 f g => i /=. unseal. by apply fun_extI.
  - intros A P x y=> i /=. by apply sig_equivI_1.
  - intros A a b ? i => /=. unseal. by apply discrete_eq_1.
  - intros A x y i => /=. unseal. by apply later_equivI_1.
  - intros A x y i => /=. unseal. by apply later_equivI_2.
Qed.
Global Instance monPred_bi_internal_eq `{BiInternalEq PROP} : BiInternalEq monPredI :=
  {| bi_internal_eq_mixin := monPred_internal_eq_mixin |}.

Global Instance monPred_bi_embed_internal_eq `{BiInternalEq PROP} :
  BiEmbedInternalEq PROP monPredI.
Proof. move=> i. rewrite monPred_internal_eq_eq. by unseal. Qed.

Lemma monPred_internal_eq_unfold `{!BiInternalEq PROP} :
  @internal_eq monPredI _ = λ A x y, ⎡ x ≡ y ⎤%I.
Proof. rewrite monPred_internal_eq_eq. by unseal. Qed.

Lemma monPred_at_internal_eq `{!BiInternalEq PROP} {A : ofeT} i (a b : A) :
  @monPred_at (a ≡ b) i ⊣⊢ a ≡ b.
Proof. rewrite monPred_internal_eq_unfold. by apply monPred_at_embed. Qed.

Lemma monPred_equivI `{!BiInternalEq PROP'} P Q :
  P ≡ Q ⊣⊢@{PROP'} ∀ i, P i ≡ Q i.
Proof.
  apply bi.equiv_spec. split.
  - apply bi.forall_intro=> ?. apply (f_equivI (flip monPred_at _)).
  - rewrite -{2}(monPred_to_from P) -{2}(monPred_to_from Q).
    rewrite -(f_equivI monPred_to).
    by rewrite !(discrete_fun_equivI P Q).
Qed.

Global Instance internal_eq_objective `{!BiInternalEq PROP} {A : ofeT} (x y : A) :
  @Objective I PROP (x ≡ y).
Proof. intros ??. rewrite monPred_internal_eq_unfold. by unseal. Qed.

(** FUpd  *)
Definition monPred_fupd_def `{BiFUpd PROP} (E1 E2 : coPset)
        (P : monPred) : monPred :=
  MonPred (λ i, |={E1,E2}=> P i)%I.
Definition monPred_fupd_aux : seal (@monPred_fupd_def). Proof. by eexists. Qed.
Definition monPred_fupd := monPred_fupd_aux.(unseal).
Local Arguments monPred_fupd {_}.
Lemma monPred_fupd_eq `{BiFUpd PROP} : @fupd _ monPred_fupd = monPred_fupd_def.
Proof. rewrite -monPred_fupd_aux.(seal_eq) //. Qed.

Lemma monPred_fupd_mixin `{BiFUpd PROP} : BiFUpdMixin monPredI monPred_fupd.
Proof.
  split; rewrite monPred_fupd_eq.
  - split=>/= i. solve_proper.
  - intros E1 E2 P HE12 =>/= i. by apply fupd_intro_mask.
  - intros E1 E2 P =>/= i. by rewrite monPred_at_except_0 except_0_fupd.
  - intros E1 E2 P Q HPQ i => /=. by rewrite HPQ.
  - intros E1 E2 E3 P i =>/=. apply fupd_trans.
  - intros E1 E2 Ef P HE1f i =>/=.
    rewrite monPred_impl_force monPred_at_pure -fupd_mask_frame_r' //.
  - intros E1 E2 P Q i =>/=. by rewrite !monPred_at_sep /= fupd_frame_r.
Qed.
Global Instance monPred_bi_fupd `{BiFUpd PROP} : BiFUpd monPredI :=
  {| bi_fupd_mixin := monPred_fupd_mixin |}.
Global Instance monPred_bi_bupd_fupd `{BiBUpdFUpd PROP} : BiBUpdFUpd monPredI.
Proof.
  intros E P i. rewrite monPred_at_bupd monPred_fupd_eq bupd_fupd //=.
Qed.
Global Instance monPred_bi_embed_fupd `{BiFUpd PROP} : BiEmbedFUpd PROP monPredI.
Proof. split=>i /=. by rewrite monPred_fupd_eq. Qed.

Lemma monPred_at_fupd `{BiFUpd PROP} i E1 E2 P :
  (|={E1,E2}=> P) i ⊣⊢ |={E1,E2}=> P i.
Proof. by rewrite monPred_fupd_eq. Qed.

Global Instance fupd_objective E1 E2 P `{!Objective P} `{BiFUpd PROP} :
  Objective (|={E1,E2}=> P)%I.
Proof. intros ??. by rewrite !monPred_at_fupd objective_at. Qed.

(** Plainly *)
Definition monPred_plainly_def `{BiPlainly PROP} P : monPred :=
  MonPred (λ _, ∀ i, ■ (P i))%I.
Definition monPred_plainly_aux : seal (@monPred_plainly_def). Proof. by eexists. Qed.
Definition monPred_plainly := monPred_plainly_aux.(unseal).
Local Arguments monPred_plainly {_}.
Lemma monPred_plainly_eq `{BiPlainly PROP} : @plainly _ monPred_plainly = monPred_plainly_def.
Proof. rewrite -monPred_plainly_aux.(seal_eq) //. Qed.

Lemma monPred_plainly_mixin `{BiPlainly PROP} : BiPlainlyMixin monPredI monPred_plainly.
Proof.
  split; rewrite monPred_plainly_eq; try unseal.
  - by (split=> ? /=; repeat f_equiv).
  - intros P Q ? i => /=. by do 3 f_equiv.
  - intros P => i /=. by rewrite bi.forall_elim plainly_elim_persistently.
  - intros P => i /=. do 3 setoid_rewrite <-plainly_forall.
    rewrite -plainly_idemp_2. f_equiv. by apply bi.forall_intro=>_.
  - intros A Ψ=> i /=. apply bi.forall_intro=> j.
    rewrite plainly_forall. apply bi.forall_intro=> a. by rewrite !bi.forall_elim.
  - intros P Q i =>/=.
    setoid_rewrite <-plainly_forall.
    apply persistently_impl_plainly.
  - intros P Q i =>/=.
    do 2 setoid_rewrite <-plainly_forall.
    setoid_rewrite plainly_impl_plainly. f_equiv.
    do 1 apply bi.forall_intro => ?. f_equiv. rewrite bi.forall_elim //.
  - intros P i =>/=. apply bi.forall_intro=>_. by apply plainly_emp_intro.
  - intros P Q i. apply bi.sep_elim_l, _.
  - intros P i =>/=.
    rewrite bi.later_forall. f_equiv=> j. by rewrite -later_plainly_1.
  - intros P i =>/=.
    rewrite bi.later_forall. f_equiv=> j. by rewrite -later_plainly_2.
Qed.
Global Instance monPred_bi_plainly `{BiPlainly PROP} : BiPlainly monPredI :=
  {| bi_plainly_mixin := monPred_plainly_mixin |}.

Global Instance monPred_bi_prop_ext
  `{!BiPlainly PROP, !BiInternalEq PROP, !BiPropExt PROP} : BiPropExt monPredI.
Proof.
  intros P Q i =>/=. rewrite monPred_plainly_eq monPred_internal_eq_eq /=.
  rewrite /bi_wand_iff monPred_equivI. f_equiv=> j. unseal.
  by rewrite prop_ext.
Qed.

(* Global Instance monPred_bi_plainly_exist `{!BiPlainly PROP} `{!BiIndexBottom bot} :
  BiPlainlyExist PROP → BiPlainlyExist monPredI.
Proof.
  split=> ? /=. rewrite monPred_plainly_eq /=. setoid_rewrite monPred_at_exist.
  rewrite (bi.forall_elim bot) plainly_exist_1. do 2 f_equiv.
  apply bi.forall_intro=>?. by do 2 f_equiv.
Qed. *)

Global Instance monPred_bi_embed_plainly `{BiPlainly PROP} :
  BiEmbedPlainly PROP monPredI.
Proof.
  split=> i. rewrite monPred_plainly_eq; unseal. apply (anti_symm _).
  - by apply bi.forall_intro.
  - by rewrite (bi.forall_elim inhabitant).
Qed.

Global Instance monPred_bi_bupd_plainly `{BiBUpdPlainly PROP} : BiBUpdPlainly monPredI.
Proof.
  intros P i.
  rewrite monPred_at_bupd monPred_plainly_eq /= bi.forall_elim. apply bupd_plainly.
Qed.

Lemma monPred_plainly_unfold `{BiPlainly PROP} : plainly = λ P, ⎡ ∀ i, ■ (P i) ⎤%I.
Proof. by rewrite monPred_plainly_eq . Qed.
Lemma monPred_at_plainly `{BiPlainly PROP} i P : (■ P) i ⊣⊢ ∀ j, ■ (P j).
Proof. by rewrite monPred_plainly_eq. Qed.

Global Instance monPred_at_plain `{BiPlainly PROP} P i : Plain P → Plain (P i).
Proof. move => /(_ i). rewrite /Plain monPred_at_plainly bi.forall_elim //. Qed.

Global Instance monPred_bi_fupd_plainly `{BiFUpdPlainly PROP} : BiFUpdPlainly monPredI.
Proof.
  split; rewrite !monPred_fupd_eq; try unseal.
  - intros E P i => /=.
    by rewrite monPred_at_plainly (bi.forall_elim i) fupd_plainly_mask_empty.
  - intros E P R i =>/=.
    by rewrite monPred_at_plainly (bi.forall_elim i) fupd_plainly_keep_l.
  - intros E P i =>/=.
    by rewrite monPred_at_plainly (bi.forall_elim i) fupd_plainly_later.
  - intros E A Φ i =>/=.
    rewrite -fupd_plainly_forall_2. apply bi.forall_mono=> x.
    by rewrite monPred_at_plainly (bi.forall_elim i).
Qed.

Global Instance plainly_objective `{BiPlainly PROP} P : Objective (■ P).
Proof. rewrite monPred_plainly_unfold. apply _. Qed.
Global Instance plainly_if_objective `{BiPlainly PROP} P p `{!Objective P} :
  Objective (■?p P).
Proof. rewrite /plainly_if. destruct p; apply _. Qed.

Global Instance monPred_objectively_plain `{BiPlainly PROP} P : Plain P → Plain (<obj> P).
Proof. rewrite monPred_objectively_unfold. apply _. Qed.
Global Instance monPred_subjectively_plain `{BiPlainly PROP} P : Plain P → Plain (<subj> P).
Proof. rewrite monPred_subjectively_unfold. apply _. Qed.
End bi_facts.
