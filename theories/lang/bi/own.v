
(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

(* TODO: LICENSE for Iris. *)

(** Extraction of own that doesn't depend on iProp. **)

Require Import iris.bi.bi.
Require Import iris.algebra.cmra.
Require Import iris.bi.embedding.
Require Import iris.si_logic.siprop.
Require Export iris.si_logic.bi.

Require Import iris.proofmode.classes.

Require Import iris.base_logic.lib.iprop.
Require Import iris.base_logic.lib.own.


(* Step-indexed Validity *)
(* This would be a little bit simpler if cmra_validN was actually an [siProp] *)
Program Definition si_valid
  {PROP : bi} `{!BiEmbed siPropI PROP} {A : cmraT} (a : A) : PROP :=
  embed {| siProp_holds n := ✓{n} a |}.
Next Obligation. simpl. intros. by eapply cmra_validN_le. Qed.

Notation "✓ x" := (si_valid x) (at level 20) : bi_scope.

Instance si_valid_plain
  {PROP : bi} `{!BiEmbed siPropI PROP} `{BiPlainly PROP}
  {BEP : BiEmbedPlainly siPropI PROP} {A : cmraT} (a : A) :
  Plain (✓ a) := _.

Instance si_valid_persistent
  {PROP : bi} `{!BiEmbed siPropI PROP} {A : cmraT} (a : A) :
  Persistent (✓ a) := _.

(* own *)
Class HasOwn {PROP : bi} {A : cmraT} : Type := {
  own           : gname → A → PROP ;
  own_op        : ∀ γ (a b : A), own γ (a ⋅ b) ⊣⊢ own γ a ∗ own γ b ;
  own_mono      : ∀ γ, Proper (flip (≼) ==> (⊢)) (own γ) ;
  own_ne        : ∀ γ, NonExpansive (own γ) ;
  own_timeless  : ∀ γ (a : A), Discrete a → Timeless (own γ a) ;
  own_core_persistent : ∀ γ a, CoreId a → Persistent (own γ a)
}.

Arguments HasOwn : clear implicits.
Arguments own {_ _ _} _ _.

Existing Instances own_mono own_timeless own_ne.

Instance own_proper `{!HasOwn PROP A} γ :
  Proper ((≡) ==> (⊣⊢)) (@own PROP A _ γ) := ne_proper _.

(* own_valid *)
Class HasOwnValid `{!BiEmbed siPropI PROP} `{!HasOwn PROP A} : Type := {
  own_valid : ∀ γ (a : A), own γ a ⊢ ✓ a
}.
Arguments HasOwnValid _ {_} _{_}.

(* own_update and own_alloc *)
Class HasOwnUpd
  `{!BiEmbed siPropI PROP} `{!BiBUpd PROP} `{!HasOwn PROP A} : Type := {
  (* TODO: we might need own_updateP *)
  own_update γ (a a' : A) : a ~~> a' -> own γ a ==∗ own γ a' ;
  own_alloc_strong_dep (f : gname → A) (P : gname → Prop) :
    pred_infinite P → (∀ γ, P γ → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ own γ (f γ)
}.
Arguments HasOwnUpd _ {_ _} _ {_}.

Class HasOwnUnit
  `{!BiEmbed siPropI PROP} `{!BiBUpd PROP} {A : ucmraT} `{!HasOwn PROP A} : Type := {
  own_unit γ : ⊢ |==> own γ (ε:A)
}.
Arguments HasOwnUnit _ {_ _} _ {_}.


Import bi.

Section valid.
  Context `{BE: !BiEmbed siPropI PROP} {A : cmraT}.
  Implicit Type (a : A) (P : PROP).

  Local Arguments siProp_holds !_ _ /.

  Local Ltac unseal :=
    constructor => n /=;
      rewrite /bi_pure /bi_and /bi_forall /=
              ?siProp_pure_eq ?siProp_and_eq ?siProp_forall_eq /=.

  (* Duplicates from Iris's base_logic.upred, but more general. *)
  (* TODO: need more lemmas for valid *)
  Lemma cmra_valid_intro P (a : A) : ✓ a → P ⊢ ✓ a.
  Proof.
    intros VL.
    (* stupid proof that relies on embedding *)
    rewrite (bi.True_intro P) -embed_pure. apply embed_mono.
    unseal => ?. by apply cmra_valid_validN.
  Qed.
  Lemma cmra_valid_elim (a : A) : ¬ ✓{0} a → ✓ a ⊢ False.
  Proof.
    intros NVL. rewrite -embed_pure. apply embed_mono.
    unseal => ?. apply NVL. apply cmra_validN_le with n; auto. lia.
  Qed.
  Lemma plainly_cmra_valid_1 `{!BiPlainly PROP} `{!@BiEmbedPlainly siPropI PROP BE _ _}
    (a : A) : ✓ a ⊢ ■ ✓ a.
  Proof. by rewrite -embed_plainly. Qed.
  Lemma cmra_valid_weaken (a b : A) : ✓ (a ⋅ b) ⊢ ✓ a.
  Proof. apply embed_mono. unseal. apply cmra_validN_op_l. Qed.

  Lemma prod_validI {B : cmraT} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
  Proof. rewrite -embed_and. apply embed_proper. by unseal. Qed.
  Lemma option_validI (mx : option A) :
    ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True end.
  Proof. destruct mx; [|rewrite -embed_pure]; apply embed_proper; by unseal. Qed.

  Lemma discrete_valid `{!CmraDiscrete A} (a : A) : ✓ a ⊣⊢ ⌜✓ a⌝.
  Proof.
    rewrite -embed_pure. apply embed_proper. unseal.
    by rewrite -cmra_discrete_valid_iff.
  Qed.

  Lemma discrete_fun_validI {B : A → ucmraT} (g : discrete_fun B) : ✓ g ⊣⊢ ∀ i, ✓ g i.
  Proof. rewrite -embed_forall. apply embed_proper. by unseal. Qed.

  (* Duplicates from base_logic.proofmode *)
  Global Instance into_pure_cmra_valid `{!CmraDiscrete A} (a : A) :
    IntoPure (✓ a) (✓ a).
  Proof. by rewrite /IntoPure discrete_valid. Qed.

  Global Instance from_pure_cmra_valid (a : A) :
    FromPure false (✓ a) (✓ a).
  Proof.
    rewrite /FromPure /=. eapply bi.pure_elim=> // ?.
    rewrite -cmra_valid_intro //.
  Qed.
End valid.

Section own_valid.
  Context `{!BiEmbed siPropI PROP} `{!HasOwn PROP A} `{!HasOwnValid PROP A}.
  Implicit Type (a : A) (P : PROP).

  (* Duplicates from base_logic.lib.own *)
  Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -∗ ✓ (a1 ⋅ a2).
  Proof. apply wand_intro_r. by rewrite -own_op own_valid. Qed.
  Lemma own_valid_3 γ a1 a2 a3 :
    own γ a1 -∗ own γ a2 -∗ own γ a3 -∗ ✓ (a1 ⋅ a2 ⋅ a3).
  Proof. do 2 apply wand_intro_r. by rewrite -!own_op own_valid. Qed.
  Lemma own_valid_r γ a : own γ a ⊢ own γ a ∗ ✓ a.
  Proof. apply: bi.persistent_entails_r. apply own_valid. Qed.
  Lemma own_valid_l γ a : own γ a ⊢ ✓ a ∗ own γ a.
  Proof. by rewrite comm -own_valid_r. Qed.

End own_valid.

Require Import iris.bi.derived_laws.
Import bi.

Section update.
  Context `{!BiEmbed siPropI PROP} `{!BiBUpd PROP} `{!HasOwn PROP A} `{!HasOwnUpd PROP A}.
  Implicit Type (a : A).

  (* Duplicates from base_logic.lib.own. *)
  Lemma own_alloc_cofinite_dep (f : gname → A) (G : gset gname) :
    (∀ γ, γ ∉ G → ✓ (f γ)) → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∧ own γ (f γ).
  Proof.
    intros Ha.
    apply (own_alloc_strong_dep f (λ γ, γ ∉ G))=> //.
    apply (pred_infinite_set (C:=gset gname)).
    intros E. set (i := fresh (G ∪ E)).
    exists i. apply not_elem_of_union, is_fresh.
  Qed.
  Lemma own_alloc_dep (f : gname → A) :
    (∀ γ, ✓ (f γ)) → ⊢ |==> ∃ γ, own γ (f γ).
  Proof.
    intros Ha. rewrite /bi_emp_valid (own_alloc_cofinite_dep f ∅) //; [].
    apply bupd_mono, exist_mono=>?. eauto using and_elim_r.
  Qed.

  Lemma own_alloc_strong a (P : gname → Prop) :
    pred_infinite P →
    ✓ a → ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ own γ a.
  Proof. intros HP Ha. eapply own_alloc_strong_dep with (f := λ _, a); eauto. Qed.
  Lemma own_alloc_cofinite a (G : gset gname) :
    ✓ a → ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∧ own γ a.
  Proof. intros Ha. eapply own_alloc_cofinite_dep with (f := λ _, a); eauto. Qed.
  Lemma own_alloc a : ✓ a → ⊢ |==> ∃ γ, own γ a.
  Proof. intros Ha. eapply own_alloc_dep with (f := λ _, a); eauto. Qed.

  Lemma own_update_2 γ a1 a2 a' :
    a1 ⋅ a2 ~~> a' → own γ a1 -∗ own γ a2 ==∗ own γ a'.
  Proof. intros. apply wand_intro_r. rewrite -own_op. by apply own_update. Qed.
  Lemma own_update_3 γ a1 a2 a3 a' :
    a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 -∗ own γ a2 -∗ own γ a3 ==∗ own γ a'.
  Proof. intros. do 2 apply wand_intro_r. rewrite -!own_op. by apply own_update. Qed.
End update.

(** Instances *)
(* Instances for iProp *)

(* Embedding of si in iProp. It seems that such an embedding doesn't exist
  upstream yet. *)
Section si_embedding.
  Context {Σ : gFunctors}.

  #[local] Arguments siProp_holds !_ _ /.
  #[local] Arguments uPred_holds !_ _ _ /.

  Notation iPropI := (iPropI Σ).
  Notation iProp := (iProp Σ).

  #[global] Program Instance si_embed : Embed siPropI iPropI :=
    λ P, {| uPred_holds n x := P n |}.
  Solve Obligations with naive_solver eauto using siProp_closed.

  #[global] Instance si_embed_mono : Proper ((⊢) ==> (⊢)) (@embed siPropI _ _).
  Proof. intros ?? PQ. constructor => ??? /=. by apply PQ. Qed.

  #[global] Instance si_embed_ne : NonExpansive (@embed siPropI _ _).
  Proof. intros ??? EQ. constructor => ???? /=. by apply EQ. Qed.

  Program Definition si_unembed (P : iProp) : siProp :=
    {| siProp_holds n := P n ε |}.
  Next Obligation. simpl. intros P n1 n2 ??. by eapply uPred_mono; eauto. Qed.
  Instance si_unembed_ne : NonExpansive si_unembed.
  Proof. intros ??? EQ. constructor => ??. rewrite /=. by apply EQ. Qed.

  Lemma si_embed_unembed (P : siProp) : si_unembed (embed P) ≡ P.
  Proof. by constructor. Qed.

  Definition siProp_embedding_mixin : BiEmbedMixin siPropI iPropI si_embed.
  Proof.
    split; try apply _.
    - intros P [EP]. constructor => ??. apply (EP _ ε). done.
      by rewrite /bi_emp /= /uPred_emp /= uPred_pure_eq /=.
    - intros PROP' IN P Q.
      rewrite -{2}(si_embed_unembed P) -{2}(si_embed_unembed Q).
      apply (f_equivI si_unembed).
    - constructor => ?? /= ??.
      by rewrite /bi_emp /= /siProp_emp /= siProp_pure_eq /=.
    - intros P Q.
      constructor => ? x ? /=.
      rewrite /bi_impl /= uPred_impl_eq /bi_impl /= siProp_impl_eq /= => PQ ??.
      apply (PQ _ x); [done|done|by eapply cmra_validN_le].
    - intros A Φ. constructor => ??? /=.
      by rewrite /bi_forall /= uPred_forall_eq /= /bi_forall /= siProp_forall_eq /=.
    - intros A Φ. constructor => ??? /=.
      by rewrite /bi_exist /= siProp_exist_eq /bi_exist /= uPred_exist_eq /=.
    - intros P Q. constructor => ? x ?.
      rewrite /bi_sep /= /siProp_sep siProp_and_eq /bi_sep /= uPred_sep_eq /=.
      split; last naive_solver.
      intros []. exists ε, x. by rewrite left_id.
    - intros P Q. constructor => ? x ?.
      rewrite /bi_wand /= uPred_wand_eq /bi_wand /= /siProp_wand siProp_impl_eq /=
        => PQ ??.
      apply (PQ _ ε); [done|rewrite right_id; by eapply cmra_validN_le].
    - intros P. constructor => ? x ?.
      by rewrite /bi_persistently /= /siProp_persistently /bi_persistently /=
                  uPred_persistently_eq.
  Qed.
  #[global] Instance siProp_bi_embed : BiEmbed siPropI iPropI :=
    {| bi_embed_mixin := siProp_embedding_mixin |}.
  #[global] Instance siProp_bi_embed_emp : BiEmbedEmp siPropI iPropI.
  Proof. constructor. intros. by rewrite /bi_emp /= /uPred_emp uPred_pure_eq. Qed.
End si_embedding.

Section iprop_instances.
  Context `{Hin: inG Σ A}.

  Notation iPropI := (iPropI Σ).

  #[global] Instance has_own_iprop : HasOwn iPropI A := {|
    own := base_logic.lib.own.own ;
    own_op := base_logic.lib.own.own_op ;
    own_mono := base_logic.lib.own.own_mono ;
    own_ne := base_logic.lib.own.own_ne ;
    own_timeless := base_logic.lib.own.own_timeless ;
    own_core_persistent := base_logic.lib.own.own_core_persistent ;
  |}.

  #[local] Arguments siProp_holds !_ _ /.
  #[local] Arguments uPred_holds !_ _ _ /.

  Lemma uPred_cmra_valid_prop_valid (a : A) :
    (uPred_cmra_valid a : iProp Σ) ⊣⊢ si_valid a.
  Proof. constructor => n x ? /=. by rewrite uPred_cmra_valid_eq. Qed.

  #[global] Instance has_own_valid_iprop : HasOwnValid iPropI A.
  Proof.
    constructor. intros. rewrite -uPred_cmra_valid_prop_valid.
    by rewrite /own /= base_logic.lib.own.own_valid.
  Qed.

  #[global] Instance has_own_update_iprop : HasOwnUpd iPropI A.
  Proof.
    constructor; rewrite /own /=.
    - by apply base_logic.lib.own.own_update.
    - by apply base_logic.lib.own.own_alloc_strong_dep.
  Qed.
End iprop_instances.

Instance has_own_unit_iprop {Σ} {A : ucmraT} `{Hin: inG Σ A} :
  HasOwnUnit (iPropI Σ) A.
Proof. constructor; rewrite /own /=. by apply base_logic.lib.own.own_unit. Qed.


(* Instances for monpred *)
Require Import iris.bi.monpred.

Section si_monpred_embedding.
  Context {I : biIndex} {Σ : gFunctors}.

  Notation monPred := (monPred I (iPropI Σ)).
  Notation monPredI := (monPredI I (iPropI Σ)).

  #[local] Arguments siProp_holds !_ _ /.
  #[local] Arguments uPred_holds !_ _ _ /.

  #[global] Instance si_monpred_embed : Embed siPropI monPredI :=
    λ P, embed (embed P).

  #[local] Ltac un_membed := rewrite /embed /si_monpred_embed /=.

  #[global] Instance si_monpred_embed_mono :
    Proper ((⊢) ==> (⊢)) (@embed siPropI monPredI _).
  Proof. intros ?? PQ. un_membed. by rewrite PQ. Qed.

  #[global] Instance si_monpred_embed_ne : NonExpansive (@embed siPropI monPredI _).
  Proof. un_membed. solve_proper. Qed.

  (* TODO: generalize to embedding of embedding *)
  Definition siProp_monpred_embedding_mixin :
    BiEmbedMixin siPropI monPredI si_monpred_embed.
  Proof.
    split; try apply _; un_membed.
    - intros P ?%bi_embed_mixin_emp_valid_inj%bi_embed_mixin_emp_valid_inj;
        [done|apply siProp_embedding_mixin|apply monPred_embedding_mixin].
    - intros PROP' IN P Q.
      rewrite !bi_embed_mixin_interal_inj;
        [done|apply siProp_embedding_mixin|apply monPred_embedding_mixin].
    - rewrite -!bi_embed_mixin_emp_2;
        [done|apply monPred_embedding_mixin|apply siProp_embedding_mixin].
    - intros P Q.
      rewrite !bi_embed_mixin_impl_2;
        [done|apply siProp_embedding_mixin|apply monPred_embedding_mixin].
    - intros A Φ.
      rewrite !bi_embed_mixin_forall_2;
        [done|apply siProp_embedding_mixin|apply monPred_embedding_mixin].
    - intros A Φ.
      rewrite !bi_embed_mixin_exist_1;
        [done|apply monPred_embedding_mixin|apply siProp_embedding_mixin].
    - intros P Q.
      rewrite !bi_embed_mixin_sep;
        [done|apply monPred_embedding_mixin|apply siProp_embedding_mixin].
    - intros P Q.
      rewrite !bi_embed_mixin_wand_2;
        [done|apply siProp_embedding_mixin|apply monPred_embedding_mixin].
    - intros P.
      rewrite {1}bi_embed_mixin_persistently; [|apply siProp_embedding_mixin].
      rewrite {1}bi_embed_mixin_persistently; [done|apply monPred_embedding_mixin].
  Qed.

  #[global] Instance siProp_bi_monpred_embed : BiEmbed siPropI monPredI :=
    {| bi_embed_mixin := siProp_monpred_embedding_mixin |}.
  #[global] Instance siProp_bi_monpred_embed_emp : BiEmbedEmp siPropI monPredI.
  Proof.
    rewrite /BiEmbedEmp {1}/embed /bi_embed_embed /= /si_monpred_embed /=.
    rewrite -embed_emp_1. apply embed_mono. by rewrite -embed_emp_1.
  Qed.
End si_monpred_embedding.

Section monpred_instances.
  Context {I : biIndex} `{Hin: inG Σ A}.

  Notation iPropI := (iPropI Σ).
  Notation monPred := (monPred I iPropI).
  Notation monPredI := (monPredI I iPropI).

  #[global] Program Instance has_own_monpred : HasOwn monPredI A := {|
    own := λ γ a , ⎡ own γ a ⎤%I |}.
  Next Obligation. intros. by rewrite -embed_sep -own_op. Qed.
  Next Obligation. solve_proper. Qed.
  Next Obligation. solve_proper. Qed.

  #[local] Ltac unseal_monpred :=
    constructor; intros; rewrite /own; red; rewrite /has_own_monpred.

  #[global] Instance has_own_valid_monpred: HasOwnValid monPredI A.
  Proof. unseal_monpred. by rewrite own_valid. Qed.

  #[global] Instance has_own_update_monpred : HasOwnUpd monPredI A.
  Proof.
    unseal_monpred.
    - by rewrite -embed_bupd own_update.
    - setoid_rewrite <-(@embed_pure iPropI). setoid_rewrite <-(@embed_and iPropI).
      setoid_rewrite <-embed_exist. rewrite -embed_bupd -(@embed_emp iPropI).
      by rewrite -own_alloc_strong_dep.
  Qed.
End monpred_instances.

Instance has_own_unit_monpred {I : biIndex} {Σ} {A : ucmraT} `{Hin: inG Σ A} :
  HasOwnUnit (monPredI I (iPropI Σ)) A.
Proof.
  constructor; intros; rewrite /own; red; rewrite /has_own_monpred.
  by rewrite -(@embed_emp (iPropI _)) -embed_bupd own_unit.
Qed.
