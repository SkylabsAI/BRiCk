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

(* A simplification of [monPred] that assumes equality on the argument and doesn't seal. *)

#[local] Set Default Proof Using "Type".
#[local] Set Suggest Proof Using.

Structure biIndex :=
  BiIndex
    { bi_index_type :> Type;
      bi_index_inhabited : Inhabited bi_index_type; }.
Existing Instances bi_index_inhabited.

Record pointPred {I : biIndex} {PROP : bi} :=
  PointPred { pointPred_at :> I → PROP }.
Bind Scope bi_scope with pointPred.

#[global] Arguments pointPred _ _ : clear implicits, assert.
#[global] Arguments PointPred {_ _} _%I : assert.
(* Simplification! *)
#[global] Arguments pointPred_at {I} {PROP} !_ _ / : assert.

Section Ofe_Cofe.
Context {I : biIndex} {PROP : bi}.
#[local] Notation pointPred := (pointPred I PROP).
Implicit Types i : I.
Implicit Types P Q : pointPred.

(** Ofe + Cofe instances  *)

Section Ofe_Cofe_def.
  Inductive pointPred_equiv' P Q : Prop :=
    { pointPred_in_equiv i : P i ≡ Q i } .
  #[local] Instance pointPred_equiv : Equiv pointPred := pointPred_equiv'.
  Inductive pointPred_dist' (n : nat) (P Q : pointPred) : Prop :=
    { pointPred_in_dist i : P i ≡{n}≡ Q i }.
  #[local] Instance pointPred_dist : Dist pointPred := pointPred_dist'.

  (* These two lemma use the wrong Equiv and Dist instance for
    pointPred. so we make sure they are not accessible outside of the
    section by using Let. *)
  Let pointPred_sig_equiv P Q : P ≡ Q ↔ pointPred_at P ≡@{I-d>PROP} pointPred_at Q.
  Proof. by split; [intros []|]. Qed.
  Let pointPred_sig_dist n (P Q : pointPred) : P ≡{n}≡ Q ↔ pointPred_at P ≡{n}@{I-d>PROP}≡ pointPred_at Q.
  Proof. by split; [intros []|]. Qed.

  Definition pointPred_ofe_mixin : OfeMixin pointPred.
  Proof. apply (iso_ofe_mixin (A:=I-d>PROP) pointPred_at pointPred_sig_equiv pointPred_sig_dist). Qed.

  Canonical Structure pointPredO := OfeT pointPred pointPred_ofe_mixin.

  Global Instance pointPred_cofe `{Cofe PROP} : Cofe pointPredO.
  Proof. exact: (iso_cofe (A:=I-d>PROP) PointPred pointPred_at). Qed.
End Ofe_Cofe_def.

  Global Instance pointPred_at_ne :
    ∀ n, Proper (dist n ==> (=) ==> dist n) pointPred_at.
  Proof. by intros ??? [Hd] ?? ->. Qed.
  Global Instance pointPred_at_proper :
    Proper ((≡) ==> (=) ==> (≡)) pointPred_at.
  Proof. repeat intro. subst. apply equiv_dist=>?. f_equiv => //. by apply equiv_dist. Qed.

Definition pointPred_to (f : I -d> PROP) : pointPredO := PointPred f.
Definition pointPred_from (f : pointPredO) : I -d> PROP := pointPred_at f.

#[global] Instance pointPred_to_ne : NonExpansive pointPred_to.
Proof. intros ????. by split => ?. Qed.
#[global] Instance pointPred_to_proper : Proper ((≡) ==> (≡)) pointPred_to.
Proof. apply: ne_proper. Qed.

#[global] Instance pointPred_from_ne : NonExpansive pointPred_from.
Proof. solve_proper. Qed.
#[global] Instance pointPred_from_proper : Proper ((≡) ==> (≡)) pointPred_from.
Proof. apply: ne_proper. Qed.

Lemma pointPred_from_to (P' : I -d> PROP) : pointPred_from (pointPred_to P') ≡ P'.
Proof. done. Qed.
Lemma pointPred_to_from P : pointPred_to (pointPred_from P) ≡ P.
Proof. done. Qed.

End Ofe_Cofe.

Global Arguments pointPredO _ _ : clear implicits.

Section Bi.
Context {I : biIndex} {PROP : bi}.
Implicit Types i : I.
Notation pointPred := (pointPred I PROP).
Implicit Types P Q : pointPred.

Definition pointPred_entails (P1 P2 : pointPred) : Prop :=
  ∀ i , P1 i ⊢ P2 i.
(* #[local] Hint Immediate pointPred_in_entails : core. *)

Definition pointPred_embed : Embed PROP pointPred := λ (P : PROP), PointPred (λ _, P).

Definition pointPred_emp : pointPred := PointPred (λ _, emp)%I.

Definition pointPred_pure (φ : Prop) : pointPred := PointPred (λ _, ⌜φ⌝)%I.

Definition pointPred_objectively_def P : pointPred := PointPred (λ _, ∀ i, P i)%I.
Definition pointPred_objectively_aux : seal (@pointPred_objectively_def). Proof. by eexists. Qed.
Definition pointPred_objectively := pointPred_objectively_aux.(unseal).
Definition pointPred_objectively_eq : @pointPred_objectively = _ := pointPred_objectively_aux.(seal_eq).

Definition pointPred_subjectively_def P : pointPred := PointPred (λ _, ∃ i, P i)%I.
Definition pointPred_subjectively_aux : seal (@pointPred_subjectively_def). Proof. by eexists. Qed.
Definition pointPred_subjectively := pointPred_subjectively_aux.(unseal).
Definition pointPred_subjectively_eq : @pointPred_subjectively = _ := pointPred_subjectively_aux.(seal_eq).

Definition pointPred_and P Q : pointPred :=
  PointPred (λ i, P i ∧ Q i)%I.

Definition pointPred_or P Q : pointPred :=
  PointPred (λ i, P i ∨ Q i)%I.

Definition pointPred_impl P Q : pointPred := PointPred (λ i, P i → Q i)%I.

Definition pointPred_forall A (Φ : A → pointPred) : pointPred :=
  PointPred (λ i, ∀ x : A, Φ x i)%I.

Definition pointPred_exist A (Φ : A → pointPred) : pointPred :=
  PointPred (λ i, ∃ x : A, Φ x i)%I.

Definition pointPred_sep P Q : pointPred :=
  PointPred (λ i, P i ∗ Q i)%I.

Definition pointPred_wand P Q : pointPred :=
  PointPred (λ i, P i -∗ Q i)%I. (* PG: No upclosure needed. *)

Definition pointPred_persistently P : pointPred :=
  PointPred (λ i, <pers> (P i))%I. (* PG: No upclosure needed. *)

Definition pointPred_in (i0 : I) : pointPred :=
  PointPred (λ i : I, <affine> ⌜i0 = i⌝)%I. (* PG: Added affinity over Iris. *)

Definition pointPred_later P : pointPred := PointPred (λ i, ▷ (P i))%I.
End Bi.

Global Arguments pointPred_objectively {_ _} _%I.
Global Arguments pointPred_subjectively {_ _} _%I.
Notation "'<obj>' P" := (pointPred_objectively P) : bi_scope.
Notation "'<subj>' P" := (pointPred_subjectively P) : bi_scope.

Module Import PointPred.
(* "unseal folding". TODO name. *)
Ltac unsealf :=
  unfold bi_affinely, bi_absorbingly, bi_except_0, bi_pure, bi_emp,
         bi_and, bi_or,
         bi_impl, bi_forall, bi_exist, bi_sep, bi_wand,
         bi_persistently, bi_affinely, bi_later; simpl.

Definition unseal_eqs :=
  (
    (* @pointPred_and_eq, @pointPred_or_eq, @pointPred_impl_eq,
   @pointPred_forall_eq, @pointPred_exist_eq, @pointPred_sep_eq, @pointPred_wand_eq,
   @pointPred_persistently_eq, @pointPred_later_eq, @pointPred_in_eq,
   @pointPred_embed_eq, @pointPred_emp_eq, @pointPred_pure_eq, *)
   @pointPred_objectively_eq, @pointPred_subjectively_eq).
Ltac unseal := unsealf; rewrite ?unseal_eqs /=.
End PointPred.

Section canonical.
Context (I : biIndex) (PROP : bi).

Lemma pointPred_bi_mixin : BiMixin (PROP:=pointPred I PROP)
  pointPred_entails pointPred_emp pointPred_pure pointPred_and pointPred_or
  pointPred_impl pointPred_forall pointPred_exist pointPred_sep pointPred_wand
  pointPred_persistently.
Proof.
  split; try by (split=> ? /=; repeat f_equiv).
  all: rewrite /pointPred_entails/=.
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

Lemma pointPred_bi_later_mixin :
  BiLaterMixin (PROP:=pointPred I PROP) pointPred_entails pointPred_pure
               pointPred_or pointPred_impl pointPred_forall pointPred_exist
               pointPred_sep pointPred_persistently pointPred_later.
Proof.
  split; unseal.
  all: rewrite /pointPred_entails/=.
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

Canonical Structure pointPredI : bi :=
  {| bi_ofe_mixin := pointPred_ofe_mixin; bi_bi_mixin := pointPred_bi_mixin;
     bi_bi_later_mixin := pointPred_bi_later_mixin |}.
End canonical.

Class Objective {I : biIndex} {PROP : bi} (P : pointPred I PROP) :=
  objective_at i j : P i -∗ P j.
Global Arguments Objective {_ _} _%I.
Global Arguments objective_at {_ _} _%I {_}.
Global Hint Mode Objective + + ! : typeclass_instances.
Global Instance: Params (@Objective) 2 := {}.


(* For now, only primitives *)
Ltac pointPredUnfold :=
  rewrite
    ?[@bi_pure (pointPredI _ _)] /bi_pure
    ?[@bi_emp (pointPredI _ _)] /bi_emp
    ?[@bi_sep (pointPredI _ _)] /bi_sep
    ?[@bi_and (pointPredI _ _)] /bi_and
    ?[@bi_or (pointPredI _ _)] /bi_or
    ?[@bi_impl (pointPredI _ _)] /bi_impl
    ?[@bi_wand (pointPredI _ _)] /bi_wand
    ?[@bi_exist (pointPredI _ _)] /bi_exist
    ?[@bi_forall (pointPredI _ _)] /bi_forall
    ?[@bi_persistently (pointPredI _ _)] /bi_persistently
    ?[@bi_later (pointPredI _ _)] /bi_later
    /=.
  (* unfold bi_affinely, bi_absorbingly, bi_except_0,
         bi_persistently, bi_affinely, bi_later; simpl. *)

Section bi_facts.
Context {I : biIndex} {PROP : bi}.
Local Notation pointPred := (pointPred I PROP).
Local Notation pointPredI := (pointPredI I PROP).
Local Notation pointPred_at := (@pointPred_at I PROP).
Implicit Types i : I.
Implicit Types P Q : pointPred.

(** pointPred_at unfolding laws *)

Lemma pointPred_at_pure i (φ : Prop) : pointPred_at ⌜φ⌝ i ⊣⊢ ⌜φ⌝.
Proof.
  (* Demonstrate simplification problem. *)
  unsealf. (* This works, but unfolds the bi structure by hand. *)
  Show.
  Undo.

  pointPredUnfold. (* This also works! And doesn't affect the proof term! *)
  Show.
  Show Proof.
  Undo.

  (* But I don't see anything else that works. *)


  cbn.
  Show.
  simpl.
  Show.
  #[global] Arguments point_pred.pointPred_at {I} {PROP} _ _ / : assert.
  simpl.
  Show.
  done.
Qed.
(* XXX Restore old setting *)
#[global] Arguments point_pred.pointPred_at {I} {PROP} !_ _ / : assert.

Lemma pointPred_at_emp i : pointPred_at emp i ⊣⊢ emp.
Proof. by unseal. Qed.
Lemma pointPred_at_and i P Q : (P ∧ Q) i ⊣⊢ P i ∧ Q i.
Proof. by unseal. Qed.
Lemma pointPred_at_or i P Q : (P ∨ Q) i ⊣⊢ P i ∨ Q i.
Proof. by unseal. Qed.
Lemma pointPred_at_impl i P Q : (P → Q) i ⊣⊢ (P i → Q i).
Proof. by unseal. Qed.
Lemma pointPred_at_forall {A} i (Φ : A → pointPred) : (∀ x, Φ x) i ⊣⊢ ∀ x, Φ x i.
Proof. by unseal. Qed.
Lemma pointPred_at_exist {A} i (Φ : A → pointPred) : (∃ x, Φ x) i ⊣⊢ ∃ x, Φ x i.
Proof. by unseal. Qed.
Lemma pointPred_at_sep i P Q : (P ∗ Q) i ⊣⊢ P i ∗ Q i.
Proof. by unseal. Qed.
Lemma pointPred_at_wand i P Q : (P -∗ Q) i ⊣⊢ (P i -∗ Q i).
Proof. by unseal. Qed.
Lemma pointPred_at_persistently i P : (<pers> P) i ⊣⊢ <pers> (P i).
Proof. by unseal. Qed.
Lemma pointPred_at_in i j : pointPred_at (pointPred_in j) i ⊣⊢ <affine> ⌜j = i⌝.
Proof. by unseal. Qed.
Lemma pointPred_at_objectively i P : (<obj> P) i ⊣⊢ ∀ j, P j.
Proof. by unseal. Qed.
Lemma pointPred_at_subjectively i P : (<subj> P) i ⊣⊢ ∃ j, P j.
Proof. by unseal. Qed.
Lemma pointPred_at_persistently_if i p P : (<pers>?p P) i ⊣⊢ <pers>?p (P i).
Proof. destruct p=>//=. Qed.
Lemma pointPred_at_affinely i P : (<affine> P) i ⊣⊢ <affine> (P i).
Proof. by rewrite /bi_affinely pointPred_at_and pointPred_at_emp. Qed.
Lemma pointPred_at_affinely_if i p P : (<affine>?p P) i ⊣⊢ <affine>?p (P i).
Proof. destruct p=>//=.  Qed.
Lemma pointPred_at_intuitionistically i P : (□ P) i ⊣⊢ □ (P i).
Proof. by rewrite /bi_intuitionistically pointPred_at_affinely pointPred_at_persistently. Qed.
Lemma pointPred_at_intuitionistically_if i p P : (□?p P) i ⊣⊢ □?p (P i).
Proof. destruct p=>//=.  Qed.

Lemma pointPred_at_absorbingly i P : (<absorb> P) i ⊣⊢ <absorb> (P i).
Proof. by rewrite /bi_absorbingly pointPred_at_sep pointPred_at_pure. Qed.
Lemma pointPred_at_absorbingly_if i p P : (<absorb>?p P) i ⊣⊢ <absorb>?p (P i).
Proof. destruct p=>//=.  Qed.

(* PG: updated. *)
Lemma pointPred_wand_force i P Q : (P -∗ Q) i ⊣⊢ (P i -∗ Q i).
Proof. exact: pointPred_at_wand. Qed.
Lemma pointPred_impl_force i P Q : (P → Q) i ⊣⊢ (P i → Q i).
Proof. exact: pointPred_at_impl. Qed.

(** Instances *)
Global Instance pointPred_at_mono :
  Proper ((⊢) ==> (=) ==> (⊢)) pointPred_at.
Proof. by move=> ?? ? ?? ->. Qed.
Global Instance pointPred_at_flip_mono :
  Proper (flip (⊢) ==> (=) ==> flip (⊢)) pointPred_at.
Proof. solve_proper. Qed.

Global Instance pointPred_in_proper :
  Proper ((=) ==> (≡)) (@pointPred_in I PROP).
Proof. unseal. split. solve_proper. Qed.
Global Instance pointPred_in_mono : Proper ((=) ==> (⊢)) (@pointPred_in I PROP).
Proof. unseal. solve_proper. Qed.
Global Instance pointPred_in_flip_mono : Proper ((=) ==> flip (⊢)) (@pointPred_in I PROP).
Proof. solve_proper. Qed.

Global Instance pointPred_pure_forall : BiPureForall PROP → BiPureForall pointPredI.
Proof. intros ? A φ i. unseal. by apply pure_forall_2. Qed.

Global Instance pointPred_later_contractive :
  BiLaterContractive PROP → BiLaterContractive pointPredI.
Proof. unseal=> ? n P Q HPQ. split=> i /=. f_contractive. apply HPQ. Qed.
Global Instance pointPred_bi_löb : BiLöb PROP → BiLöb pointPredI.
Proof. rewrite {2}/BiLöb; unseal=> ? P HP i /=. apply löb_weak, HP. Qed.
Global Instance pointPred_bi_positive : BiPositive PROP → BiPositive pointPredI.
Proof. intros ????. unseal. apply bi_positive. Qed.
Global Instance pointPred_bi_affine : BiAffine PROP → BiAffine pointPredI.
Proof. intros ???. unseal. by apply affine. Qed.

Lemma pointPred_persistent P : (∀ i, Persistent (P i)) → Persistent P.
Proof. intros HP i. unseal. apply HP. Qed.
Lemma pointPred_absorbing P : (∀ i, Absorbing (P i)) → Absorbing P.
Proof. intros HP i. unseal. apply HP. Qed.
Lemma pointPred_affine P : (∀ i, Affine (P i)) → Affine P.
Proof. intros HP i. unseal. apply HP. Qed.

Global Instance pointPred_at_persistent P i : Persistent P → Persistent (P i).
Proof. move => /(_ i). by unseal. Qed.
Global Instance pointPred_at_absorbing P i : Absorbing P → Absorbing (P i).
Proof. move => /(_ i). unfold Absorbing. by unseal. Qed.
Global Instance pointPred_at_affine P i : Affine P → Affine (P i).
Proof. move => /(_ i). unfold Affine. by unseal. Qed.

(** Note that [pointPred_in] is *not* [Plain], because it depends on the index. *)
Global Instance pointPred_in_persistent i : Persistent (@pointPred_in I PROP i).
Proof. apply pointPred_persistent=> j. rewrite pointPred_at_in. apply _. Qed.
Global Instance pointPred_in_affine i : Affine (@pointPred_in I PROP i). (* PG: was [Absorbing] *)
Proof. apply pointPred_affine=> j. rewrite pointPred_at_in. apply _. Qed.

Definition pointPred_embedding_mixin : BiEmbedMixin PROP pointPredI pointPred_embed.
Proof.
  split; try apply _; rewrite /bi_emp_valid; unseal; try done.
  - by repeat intro.
  - move=> P /= /(_ inhabitant) ? //.
  - intros PROP' ? P Q.
    set (f P := pointPred_at P inhabitant).
    assert (NonExpansive f) by solve_proper.
    apply (f_equivI f).
Qed.
Global Instance pointPred_bi_embed : BiEmbed PROP pointPredI :=
  {| bi_embed_mixin := pointPred_embedding_mixin |}.
Global Instance pointPred_bi_embed_emp : BiEmbedEmp PROP pointPredI.
Proof. intro. by unseal. Qed.

Lemma pointPred_at_embed i (P : PROP) : pointPred_at ⎡P⎤ i ⊣⊢ P.
Proof. by unseal. Qed.

Lemma pointPred_emp_unfold : emp%I = ⎡emp : PROP⎤%I.
Proof. by unseal. Qed.
Lemma pointPred_pure_unfold : bi_pure = λ φ, ⎡ ⌜ φ ⌝ : PROP⎤%I.
Proof. by unseal. Qed.
Lemma pointPred_objectively_unfold : pointPred_objectively = λ P, ⎡∀ i, P i⎤%I.
Proof. by unseal. Qed.
Lemma pointPred_subjectively_unfold : pointPred_subjectively = λ P, ⎡∃ i, P i⎤%I.
Proof. by unseal. Qed.

Global Instance pointPred_objectively_ne : NonExpansive (@pointPred_objectively I PROP).
Proof. rewrite pointPred_objectively_unfold. solve_proper. Qed.
Global Instance pointPred_objectively_proper : Proper ((≡) ==> (≡)) (@pointPred_objectively I PROP).
Proof. apply (ne_proper _). Qed.
Lemma pointPred_objectively_mono P Q : (P ⊢ Q) → (<obj> P ⊢ <obj> Q).
Proof. rewrite pointPred_objectively_unfold. solve_proper. Qed.
Global Instance pointPred_objectively_mono' : Proper ((⊢) ==> (⊢)) (@pointPred_objectively I PROP).
Proof. intros ???. by apply pointPred_objectively_mono. Qed.
Global Instance pointPred_objectively_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@pointPred_objectively I PROP).
Proof. intros ???. by apply pointPred_objectively_mono. Qed.

Global Instance pointPred_objectively_persistent P : Persistent P → Persistent (<obj> P).
Proof. rewrite pointPred_objectively_unfold. apply _. Qed.
Global Instance pointPred_objectively_absorbing P : Absorbing P → Absorbing (<obj> P).
Proof. rewrite pointPred_objectively_unfold. apply _. Qed.
Global Instance pointPred_objectively_affine P : Affine P → Affine (<obj> P).
Proof. rewrite pointPred_objectively_unfold. apply _. Qed.

Global Instance pointPred_subjectively_ne : NonExpansive (@pointPred_subjectively I PROP).
Proof. rewrite pointPred_subjectively_unfold. solve_proper. Qed.
Global Instance pointPred_subjectively_proper : Proper ((≡) ==> (≡)) (@pointPred_subjectively I PROP).
Proof. apply (ne_proper _). Qed.
Lemma pointPred_subjectively_mono P Q : (P ⊢ Q) → <subj> P ⊢ <subj> Q.
Proof. rewrite pointPred_subjectively_unfold. solve_proper. Qed.
Global Instance pointPred_subjectively_mono' : Proper ((⊢) ==> (⊢)) (@pointPred_subjectively I PROP).
Proof. intros ???. by apply pointPred_subjectively_mono. Qed.
Global Instance pointPred_subjectively_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) (@pointPred_subjectively I PROP).
Proof. intros ???. by apply pointPred_subjectively_mono. Qed.

Global Instance pointPred_subjectively_persistent P : Persistent P → Persistent (<subj> P).
Proof. rewrite pointPred_subjectively_unfold. apply _. Qed.
Global Instance pointPred_subjectively_absorbing P : Absorbing P → Absorbing (<subj> P).
Proof. rewrite pointPred_subjectively_unfold. apply _. Qed.
Global Instance pointPred_subjectively_affine P : Affine P → Affine (<subj> P).
Proof. rewrite pointPred_subjectively_unfold. apply _. Qed.

(* Laws for pointPred_objectively and of Objective. *)
Lemma pointPred_objectively_elim P : <obj> P ⊢ P.
Proof. rewrite pointPred_objectively_unfold. unseal =>?. apply bi.forall_elim. Qed.
Lemma pointPred_objectively_idemp P : <obj> <obj> P ⊣⊢ <obj> P.
Proof.
  apply bi.equiv_spec; split; [by apply pointPred_objectively_elim|].
  unseal =>i /=. by apply bi.forall_intro=>_.
Qed.

Lemma pointPred_objectively_forall {A} (Φ : A → pointPred) : <obj> (∀ x, Φ x) ⊣⊢ ∀ x, <obj> (Φ x).
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=;
    do 2 apply bi.forall_intro=>?; by do 2 rewrite bi.forall_elim.
Qed.
Lemma pointPred_objectively_and P Q : <obj> (P ∧ Q) ⊣⊢ <obj> P ∧ <obj> Q.
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=.
  - apply bi.and_intro; do 2 f_equiv.
    + apply bi.and_elim_l.
    + apply bi.and_elim_r.
  - apply bi.forall_intro=>?. by rewrite !bi.forall_elim.
Qed.
Lemma pointPred_objectively_exist {A} (Φ : A → pointPred) :
  (∃ x, <obj> (Φ x)) ⊢ <obj> (∃ x, (Φ x)).
Proof. apply bi.exist_elim=>?. f_equiv. apply bi.exist_intro. Qed.
Lemma pointPred_objectively_or P Q : <obj> P ∨ <obj> Q ⊢ <obj> (P ∨ Q).
Proof.
  apply bi.or_elim; f_equiv.
  - apply bi.or_intro_l.
  - apply bi.or_intro_r.
Qed.

Lemma pointPred_objectively_sep_2 P Q : <obj> P ∗ <obj> Q ⊢ <obj> (P ∗ Q).
Proof. unseal =>i /=. apply bi.forall_intro=>?. by rewrite !bi.forall_elim. Qed.

(* Lemma pointPred_objectively_sep_1 P Q : <obj> (P ∗ Q) ⊢ <obj> P ∗ <obj> Q.
Proof. unseal =>i /=.

Require Import iris.proofmode.tactics.
iIntros "H".

apply bi.forall_elim. =>?. by rewrite !bi.forall_elim. Qed.
Lemma pointPred_objectively_sep P Q : <obj> (P ∗ Q) ⊣⊢ <obj> P ∗ <obj> Q.
Proof.
  apply bi.equiv_spec, conj, pointPred_objectively_sep_2. unseal=>i /=.
  rewrite (bi.forall_elim j). f_equiv; apply bi.forall_intro=>j; f_equiv.
Qed. *)

Lemma pointPred_objectively_embed (P : PROP) : <obj> ⎡P⎤ ⊣⊢ ⎡P⎤.
Proof.
  apply bi.equiv_spec; split; unseal =>i /=.
  - by rewrite (bi.forall_elim inhabitant).
  - by apply bi.forall_intro.
Qed.
Lemma pointPred_objectively_emp : <obj> (emp : pointPred) ⊣⊢ emp.
Proof. rewrite pointPred_emp_unfold. apply pointPred_objectively_embed. Qed.
Lemma pointPred_objectively_pure φ : <obj> (⌜ φ ⌝ : pointPred) ⊣⊢ ⌜ φ ⌝.
Proof. rewrite pointPred_pure_unfold. apply pointPred_objectively_embed. Qed.

Lemma pointPred_subjectively_intro P : P ⊢ <subj> P.
Proof. unseal =>?. apply bi.exist_intro. Qed.

Lemma pointPred_subjectively_forall {A} (Φ : A → pointPred) :
  (<subj> (∀ x, Φ x)) ⊢ ∀ x, <subj> (Φ x).
Proof. apply bi.forall_intro=>?. f_equiv. apply bi.forall_elim. Qed.
Lemma pointPred_subjectively_and P Q : <subj> (P ∧ Q) ⊢ <subj> P ∧ <subj> Q.
Proof.
  apply bi.and_intro; f_equiv.
  - apply bi.and_elim_l.
  - apply bi.and_elim_r.
Qed.
Lemma pointPred_subjectively_exist {A} (Φ : A → pointPred) : <subj> (∃ x, Φ x) ⊣⊢ ∃ x, <subj> (Φ x).
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=;
    do 2 apply bi.exist_elim=>?; by do 2 rewrite -bi.exist_intro.
Qed.
Lemma pointPred_subjectively_or P Q : <subj> (P ∨ Q) ⊣⊢ <subj> P ∨ <subj> Q.
Proof.
  unseal. split=>i. apply bi.equiv_spec; split=>/=.
  - apply bi.exist_elim=>?. by rewrite -!bi.exist_intro.
  - apply bi.or_elim; do 2 f_equiv.
    + apply bi.or_intro_l.
    + apply bi.or_intro_r.
Qed.

Lemma pointPred_subjectively_sep P Q : <subj> (P ∗ Q) ⊢ <subj> P ∗ <subj> Q.
Proof. unseal=>i /=. apply bi.exist_elim=>?. by rewrite -!bi.exist_intro. Qed.

Lemma pointPred_subjectively_idemp P : <subj> <subj> P ⊣⊢ <subj> P.
Proof.
  apply bi.equiv_spec; split; [|by apply pointPred_subjectively_intro].
  unseal =>i /=. by apply bi.exist_elim=>_.
Qed.

Lemma objective_objectively P `{!Objective P} : P ⊢ <obj> P.
Proof.
  rewrite pointPred_objectively_unfold /= embed_forall. apply bi.forall_intro=>??.
  unseal. apply objective_at, _.
Qed.
Lemma objective_subjectively P `{!Objective P} : <subj> P ⊢ P.
Proof.
  rewrite pointPred_subjectively_unfold /= embed_exist. apply bi.exist_elim=>??.
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
Proof. intros i j. by rewrite !pointPred_at_or !(objective_at _ i j). Qed.
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

(** pointPred_in *)
Lemma pointPred_in_intro P : P ⊢ ∃ i, pointPred_in i ∗ ⎡P i⎤.
Proof.
  unseal=>i /=.
  rewrite -(bi.exist_intro i). apply bi.sep_intro_emp_valid_l => //.
  by apply /bi.affinely_intro /bi.pure_intro.
Qed.
Lemma pointPred_in_elim P i : pointPred_in i -∗ ⎡P i⎤ → P .
Proof.
  apply bi.impl_intro_r. unseal =>i' /=.
  rewrite bi.affinely_elim.
  eapply bi.pure_elim; [apply bi.and_elim_l|]=>->. apply bi.and_elim_r.
Qed.

(** Big op *)
Global Instance pointPred_at_monoid_and_homomorphism i :
  MonoidHomomorphism bi_and bi_and (≡) (flip pointPred_at i).
Proof. split; [split|]; try apply _; [apply pointPred_at_and | apply pointPred_at_pure]. Qed.
Global Instance pointPred_at_monoid_or_homomorphism i :
  MonoidHomomorphism bi_or bi_or (≡) (flip pointPred_at i).
Proof. split; [split|]; try apply _; [apply pointPred_at_or | apply pointPred_at_pure]. Qed.
Global Instance pointPred_at_monoid_sep_homomorphism i :
  MonoidHomomorphism bi_sep bi_sep (≡) (flip pointPred_at i).
Proof. split; [split|]; try apply _; [apply pointPred_at_sep | apply pointPred_at_emp]. Qed.

Lemma pointPred_at_big_sepL {A} i (Φ : nat → A → pointPred) l :
  ([∗ list] k↦x ∈ l, Φ k x) i ⊣⊢ [∗ list] k↦x ∈ l, Φ k x i.
Proof. apply (big_opL_commute (flip pointPred_at i)). Qed.
Lemma pointPred_at_big_sepM `{Countable K} {A} i (Φ : K → A → pointPred) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, Φ k x) i ⊣⊢ [∗ map] k↦x ∈ m, Φ k x i.
Proof. apply (big_opM_commute (flip pointPred_at i)). Qed.
Lemma pointPred_at_big_sepS `{Countable A} i (Φ : A → pointPred) (X : gset A) :
  ([∗ set] y ∈ X, Φ y) i ⊣⊢ [∗ set] y ∈ X, Φ y i.
Proof. apply (big_opS_commute (flip pointPred_at i)). Qed.
Lemma pointPred_at_big_sepMS `{Countable A} i (Φ : A → pointPred) (X : gmultiset A) :
  ([∗ mset] y ∈ X, Φ y) i ⊣⊢ ([∗ mset] y ∈ X, Φ y i).
Proof. apply (big_opMS_commute (flip pointPred_at i)). Qed.

Global Instance pointPred_objectively_monoid_and_homomorphism :
  MonoidHomomorphism bi_and bi_and (≡) (@pointPred_objectively I PROP).
Proof.
  split; [split|]; try apply _.
  - apply pointPred_objectively_and.
  - apply pointPred_objectively_pure.
Qed.
Global Instance pointPred_objectively_monoid_sep_entails_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (@pointPred_objectively I PROP).
Proof.
  split; [split|]; try apply _.
  - apply pointPred_objectively_sep_2.
  - by rewrite pointPred_objectively_emp.
Qed.
(* Global Instance pointPred_objectively_monoid_sep_homomorphism `{BiIndexBottom bot} :
  MonoidHomomorphism bi_sep bi_sep (≡) (@pointPred_objectively I PROP).
Proof.
  split; [split|]; try apply _.
  - apply pointPred_objectively_sep.
  - by rewrite pointPred_objectively_emp.
Qed. *)

Lemma pointPred_objectively_big_sepL_entails {A} (Φ : nat → A → pointPred) l :
  ([∗ list] k↦x ∈ l, <obj> (Φ k x)) ⊢ <obj> ([∗ list] k↦x ∈ l, Φ k x).
Proof. apply (big_opL_commute pointPred_objectively (R:=flip (⊢))). Qed.
Lemma pointPred_objectively_big_sepM_entails
      `{Countable K} {A} (Φ : K → A → pointPred) (m : gmap K A) :
  ([∗ map] k↦x ∈ m, <obj> (Φ k x)) ⊢ <obj> ([∗ map] k↦x ∈ m, Φ k x).
Proof. apply (big_opM_commute pointPred_objectively (R:=flip (⊢))). Qed.
Lemma pointPred_objectively_big_sepS_entails `{Countable A} (Φ : A → pointPred) (X : gset A) :
  ([∗ set] y ∈ X, <obj> (Φ y)) ⊢ <obj> ([∗ set] y ∈ X, Φ y).
Proof. apply (big_opS_commute pointPred_objectively (R:=flip (⊢))). Qed.
Lemma pointPred_objectively_big_sepMS_entails `{Countable A} (Φ : A → pointPred) (X : gmultiset A) :
  ([∗ mset] y ∈ X, <obj> (Φ y)) ⊢ <obj> ([∗ mset] y ∈ X, Φ y).
Proof. apply (big_opMS_commute pointPred_objectively (R:=flip (⊢))). Qed.

(* Lemma pointPred_objectively_big_sepL `{BiIndexBottom bot} {A} (Φ : nat → A → pointPred) l :
  <obj> ([∗ list] k↦x ∈ l, Φ k x) ⊣⊢ ([∗ list] k↦x ∈ l, <obj> (Φ k x)).
Proof. apply (big_opL_commute _). Qed.
Lemma pointPred_objectively_big_sepM `{BiIndexBottom bot} `{Countable K} {A}
      (Φ : K → A → pointPred) (m : gmap K A) :
  <obj> ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ([∗ map] k↦x ∈ m, <obj> (Φ k x)).
Proof. apply (big_opM_commute _). Qed.
Lemma pointPred_objectively_big_sepS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → pointPred) (X : gset A) :
  <obj> ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, <obj> (Φ y)).
Proof. apply (big_opS_commute _). Qed.
Lemma pointPred_objectively_big_sepMS `{BiIndexBottom bot} `{Countable A}
      (Φ : A → pointPred) (X : gmultiset A) :
  <obj> ([∗ mset] y ∈ X, Φ y) ⊣⊢  ([∗ mset] y ∈ X, <obj> (Φ y)).
Proof. apply (big_opMS_commute _). Qed. *)

Global Instance big_sepL_objective {A} (l : list A) Φ `{∀ n x, Objective (Φ n x)} :
  @Objective I PROP ([∗ list] n↦x ∈ l, Φ n x)%I.
Proof. generalize dependent Φ. induction l=>/=; apply _. Qed.
Global Instance big_sepM_objective `{Countable K} {A}
       (Φ : K → A → pointPred) (m : gmap K A) `{∀ k x, Objective (Φ k x)} :
  Objective ([∗ map] k↦x ∈ m, Φ k x)%I.
Proof. intros ??. rewrite !pointPred_at_big_sepM. do 3 f_equiv. by apply objective_at. Qed.
Global Instance big_sepS_objective `{Countable A} (Φ : A → pointPred)
       (X : gset A) `{∀ y, Objective (Φ y)} :
  Objective ([∗ set] y ∈ X, Φ y)%I.
Proof. intros ??. rewrite !pointPred_at_big_sepS. do 2 f_equiv. by apply objective_at. Qed.
Global Instance big_sepMS_objective `{Countable A} (Φ : A → pointPred)
       (X : gmultiset A) `{∀ y, Objective (Φ y)} :
  Objective ([∗ mset] y ∈ X, Φ y)%I.
Proof. intros ??. rewrite !pointPred_at_big_sepMS. do 2 f_equiv. by apply objective_at. Qed.

(** BUpd *)
Definition pointPred_bupd_def `{BiBUpd PROP} (P : pointPred) : pointPred :=
  PointPred (λ i, |==> P i)%I.
Definition pointPred_bupd_aux : seal (@pointPred_bupd_def). Proof. by eexists. Qed.
Definition pointPred_bupd := pointPred_bupd_aux.(unseal).
Local Arguments pointPred_bupd {_}.
Lemma pointPred_bupd_eq `{BiBUpd PROP} : @bupd _ pointPred_bupd = pointPred_bupd_def.
Proof. rewrite -pointPred_bupd_aux.(seal_eq) //. Qed.

Lemma pointPred_bupd_mixin `{BiBUpd PROP} : BiBUpdMixin pointPredI pointPred_bupd.
Proof.
  split; rewrite pointPred_bupd_eq.
  - split=>/= i. solve_proper.
  - intros P i=>/=. apply bupd_intro.
  - intros P Q HPQ i => /=. by rewrite HPQ.
  - intros P i =>/=. apply bupd_trans.
  - intros P Q i => /=. rewrite !pointPred_at_sep /=. apply bupd_frame_r.
Qed.
Global Instance pointPred_bi_bupd `{BiBUpd PROP} : BiBUpd pointPredI :=
  {| bi_bupd_mixin := pointPred_bupd_mixin |}.

Lemma pointPred_at_bupd `{BiBUpd PROP} i P : (|==> P) i ⊣⊢ |==> P i.
Proof. by rewrite pointPred_bupd_eq. Qed.

Global Instance bupd_objective `{BiBUpd PROP} P `{!Objective P} :
  Objective (|==> P)%I.
Proof. intros ??. by rewrite !pointPred_at_bupd objective_at. Qed.

Global Instance pointPred_bi_embed_bupd `{BiBUpd PROP} :
  BiEmbedBUpd PROP pointPredI.
Proof. split=>i /=. by rewrite pointPred_at_bupd !pointPred_at_embed. Qed.

(** Later *)
Global Instance pointPred_bi_embed_later : BiEmbedLater PROP pointPredI.
Proof. split; by unseal. Qed.

Global Instance pointPred_at_timeless P i : Timeless P → Timeless (P i).
Proof. move => /(_ i). unfold Timeless. by unseal. Qed.
(* PG: Timeless pulled in by affinely_timeless. *)
Global Instance pointPred_in_timeless i0 : Timeless (@bi_emp PROP) -> Timeless (@pointPred_in I PROP i0).
Proof. move => ? ? /=. unseal. apply: timeless. Qed.
(* Global Instance pointPred_in_timeless i0 : Timeless (@pointPred_in I PROP i0).
Proof. move => ? /=. unseal. apply timeless. apply _. Qed. *)
Global Instance pointPred_objectively_timeless P : Timeless P → Timeless (<obj> P).
Proof.
  unfold Timeless. unseal=>Hti ? /=.
  by apply timeless, bi.forall_timeless.
Qed.
Global Instance pointPred_subjectively_timeless P : Timeless P → Timeless (<subj> P).
Proof.
  unfold Timeless. unseal=>Hti ? /=.
  by apply timeless, bi.exist_timeless.
Qed.

Lemma pointPred_at_later i P : (▷ P) i ⊣⊢ ▷ P i.
Proof. by unseal. Qed.
Lemma pointPred_at_laterN n i P : (▷^n P) i ⊣⊢ ▷^n P i.
Proof. induction n as [|? IHn]; first done. rewrite /= pointPred_at_later IHn //. Qed.
Lemma pointPred_at_except_0 i P : (◇ P) i ⊣⊢ ◇ P i.
Proof. by unseal. Qed.

Global Instance later_objective P `{!Objective P} : Objective (▷ P).
Proof. intros ??. unseal. by rewrite objective_at. Qed.
Global Instance laterN_objective P `{!Objective P} n : Objective (▷^n P).
Proof. induction n; apply _. Qed.
Global Instance except0_objective P `{!Objective P} : Objective (◇ P).
Proof. rewrite /bi_except_0. apply _. Qed.

(** Internal equality *)
Definition pointPred_internal_eq_def `{!BiInternalEq PROP} (A : ofeT) (a b : A) : pointPred :=
  PointPred (λ _, a ≡ b)%I.
Definition pointPred_internal_eq_aux : seal (@pointPred_internal_eq_def).
Proof. by eexists. Qed.
Definition pointPred_internal_eq := pointPred_internal_eq_aux.(unseal).
Local Arguments pointPred_internal_eq {_}.
Lemma pointPred_internal_eq_eq `{!BiInternalEq PROP} :
  @internal_eq _ (@pointPred_internal_eq _) = pointPred_internal_eq_def.
Proof. rewrite -pointPred_internal_eq_aux.(seal_eq) //. Qed.

Lemma pointPred_internal_eq_mixin `{!BiInternalEq PROP} :
  BiInternalEqMixin pointPredI (@pointPred_internal_eq _).
Proof.
  split; rewrite pointPred_internal_eq_eq.
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
Global Instance pointPred_bi_internal_eq `{BiInternalEq PROP} : BiInternalEq pointPredI :=
  {| bi_internal_eq_mixin := pointPred_internal_eq_mixin |}.

Global Instance pointPred_bi_embed_internal_eq `{BiInternalEq PROP} :
  BiEmbedInternalEq PROP pointPredI.
Proof. move=> i. rewrite pointPred_internal_eq_eq. by unseal. Qed.

Lemma pointPred_internal_eq_unfold `{!BiInternalEq PROP} :
  @internal_eq pointPredI _ = λ A x y, ⎡ x ≡ y ⎤%I.
Proof. rewrite pointPred_internal_eq_eq. by unseal. Qed.

Lemma pointPred_at_internal_eq `{!BiInternalEq PROP} {A : ofeT} i (a b : A) :
  @pointPred_at (a ≡ b) i ⊣⊢ a ≡ b.
Proof. rewrite pointPred_internal_eq_unfold. by apply pointPred_at_embed. Qed.

Lemma pointPred_equivI `{!BiInternalEq PROP'} P Q :
  P ≡ Q ⊣⊢@{PROP'} ∀ i, P i ≡ Q i.
Proof.
  apply bi.equiv_spec. split.
  - apply bi.forall_intro=> ?. apply (f_equivI (flip pointPred_at _)).
  - rewrite -{2}(pointPred_to_from P) -{2}(pointPred_to_from Q).
    rewrite -(f_equivI pointPred_to).
    by rewrite !(discrete_fun_equivI P Q).
Qed.

Global Instance internal_eq_objective `{!BiInternalEq PROP} {A : ofeT} (x y : A) :
  @Objective I PROP (x ≡ y).
Proof. intros ??. rewrite pointPred_internal_eq_unfold. by unseal. Qed.

(** FUpd  *)
Definition pointPred_fupd_def `{BiFUpd PROP} (E1 E2 : coPset)
        (P : pointPred) : pointPred :=
  PointPred (λ i, |={E1,E2}=> P i)%I.
Definition pointPred_fupd_aux : seal (@pointPred_fupd_def). Proof. by eexists. Qed.
Definition pointPred_fupd := pointPred_fupd_aux.(unseal).
Local Arguments pointPred_fupd {_}.
Lemma pointPred_fupd_eq `{BiFUpd PROP} : @fupd _ pointPred_fupd = pointPred_fupd_def.
Proof. rewrite -pointPred_fupd_aux.(seal_eq) //. Qed.

Lemma pointPred_fupd_mixin `{BiFUpd PROP} : BiFUpdMixin pointPredI pointPred_fupd.
Proof.
  split; rewrite pointPred_fupd_eq.
  - split=>/= i. solve_proper.
  - intros E1 E2 P HE12 =>/= i. by apply fupd_intro_mask.
  - intros E1 E2 P =>/= i. by rewrite pointPred_at_except_0 except_0_fupd.
  - intros E1 E2 P Q HPQ i => /=. by rewrite HPQ.
  - intros E1 E2 E3 P i =>/=. apply fupd_trans.
  - intros E1 E2 Ef P HE1f i =>/=.
    rewrite pointPred_impl_force pointPred_at_pure -fupd_mask_frame_r' //.
  - intros E1 E2 P Q i =>/=. by rewrite !pointPred_at_sep /= fupd_frame_r.
Qed.
Global Instance pointPred_bi_fupd `{BiFUpd PROP} : BiFUpd pointPredI :=
  {| bi_fupd_mixin := pointPred_fupd_mixin |}.
Global Instance pointPred_bi_bupd_fupd `{BiBUpdFUpd PROP} : BiBUpdFUpd pointPredI.
Proof.
  intros E P i. rewrite pointPred_at_bupd pointPred_fupd_eq bupd_fupd //=.
Qed.
Global Instance pointPred_bi_embed_fupd `{BiFUpd PROP} : BiEmbedFUpd PROP pointPredI.
Proof. split=>i /=. by rewrite pointPred_fupd_eq. Qed.

Lemma pointPred_at_fupd `{BiFUpd PROP} i E1 E2 P :
  (|={E1,E2}=> P) i ⊣⊢ |={E1,E2}=> P i.
Proof. by rewrite pointPred_fupd_eq. Qed.

Global Instance fupd_objective E1 E2 P `{!Objective P} `{BiFUpd PROP} :
  Objective (|={E1,E2}=> P)%I.
Proof. intros ??. by rewrite !pointPred_at_fupd objective_at. Qed.

(** Plainly *)
Definition pointPred_plainly_def `{BiPlainly PROP} P : pointPred :=
  PointPred (λ _, ∀ i, ■ (P i))%I.
Definition pointPred_plainly_aux : seal (@pointPred_plainly_def). Proof. by eexists. Qed.
Definition pointPred_plainly := pointPred_plainly_aux.(unseal).
Local Arguments pointPred_plainly {_}.
Lemma pointPred_plainly_eq `{BiPlainly PROP} : @plainly _ pointPred_plainly = pointPred_plainly_def.
Proof. rewrite -pointPred_plainly_aux.(seal_eq) //. Qed.

Lemma pointPred_plainly_mixin `{BiPlainly PROP} : BiPlainlyMixin pointPredI pointPred_plainly.
Proof.
  split; rewrite pointPred_plainly_eq; try unseal.
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
Global Instance pointPred_bi_plainly `{BiPlainly PROP} : BiPlainly pointPredI :=
  {| bi_plainly_mixin := pointPred_plainly_mixin |}.

Global Instance pointPred_bi_prop_ext
  `{!BiPlainly PROP, !BiInternalEq PROP, !BiPropExt PROP} : BiPropExt pointPredI.
Proof.
  intros P Q i =>/=. rewrite pointPred_plainly_eq pointPred_internal_eq_eq /=.
  rewrite /bi_wand_iff pointPred_equivI. f_equiv=> j. unseal.
  by rewrite prop_ext.
Qed.

(* Global Instance pointPred_bi_plainly_exist `{!BiPlainly PROP} `{!BiIndexBottom bot} :
  BiPlainlyExist PROP → BiPlainlyExist pointPredI.
Proof.
  split=> ? /=. rewrite pointPred_plainly_eq /=. setoid_rewrite pointPred_at_exist.
  rewrite (bi.forall_elim bot) plainly_exist_1. do 2 f_equiv.
  apply bi.forall_intro=>?. by do 2 f_equiv.
Qed. *)

Global Instance pointPred_bi_embed_plainly `{BiPlainly PROP} :
  BiEmbedPlainly PROP pointPredI.
Proof.
  split=> i. rewrite pointPred_plainly_eq; unseal. apply (anti_symm _).
  - by apply bi.forall_intro.
  - by rewrite (bi.forall_elim inhabitant).
Qed.

Global Instance pointPred_bi_bupd_plainly `{BiBUpdPlainly PROP} : BiBUpdPlainly pointPredI.
Proof.
  intros P i.
  rewrite pointPred_at_bupd pointPred_plainly_eq /= bi.forall_elim. apply bupd_plainly.
Qed.

Lemma pointPred_plainly_unfold `{BiPlainly PROP} : plainly = λ P, ⎡ ∀ i, ■ (P i) ⎤%I.
Proof. by rewrite pointPred_plainly_eq . Qed.
Lemma pointPred_at_plainly `{BiPlainly PROP} i P : (■ P) i ⊣⊢ ∀ j, ■ (P j).
Proof. by rewrite pointPred_plainly_eq. Qed.

Global Instance pointPred_at_plain `{BiPlainly PROP} P i : Plain P → Plain (P i).
Proof. move => /(_ i). rewrite /Plain pointPred_at_plainly bi.forall_elim //. Qed.

Global Instance pointPred_bi_fupd_plainly `{BiFUpdPlainly PROP} : BiFUpdPlainly pointPredI.
Proof.
  split; rewrite !pointPred_fupd_eq; try unseal.
  - intros E P i => /=.
    by rewrite pointPred_at_plainly (bi.forall_elim i) fupd_plainly_mask_empty.
  - intros E P R i =>/=.
    by rewrite pointPred_at_plainly (bi.forall_elim i) fupd_plainly_keep_l.
  - intros E P i =>/=.
    by rewrite pointPred_at_plainly (bi.forall_elim i) fupd_plainly_later.
  - intros E A Φ i =>/=.
    rewrite -fupd_plainly_forall_2. apply bi.forall_mono=> x.
    by rewrite pointPred_at_plainly (bi.forall_elim i).
Qed.

Global Instance plainly_objective `{BiPlainly PROP} P : Objective (■ P).
Proof. rewrite pointPred_plainly_unfold. apply _. Qed.
Global Instance plainly_if_objective `{BiPlainly PROP} P p `{!Objective P} :
  Objective (■?p P).
Proof. rewrite /plainly_if. destruct p; apply _. Qed.

Global Instance pointPred_objectively_plain `{BiPlainly PROP} P : Plain P → Plain (<obj> P).
Proof. rewrite pointPred_objectively_unfold. apply _. Qed.
Global Instance pointPred_subjectively_plain `{BiPlainly PROP} P : Plain P → Plain (<subj> P).
Proof. rewrite pointPred_subjectively_unfold. apply _. Qed.
End bi_facts.
