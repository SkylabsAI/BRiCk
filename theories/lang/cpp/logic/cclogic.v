(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.prelude.base.

From iris.bi Require Import lib.fractional monpred.
From iris.base_logic.lib Require Import invariants cancelable_invariants.
From iris.proofmode Require Import tactics.

From bedrock.lang.cpp Require Import logic.pred.

Set Default Proof Using "Type".

(** This file exports the mpred version of own, inv and cinv. *)
(* Right now, they simply shadow Iris' own, inv and cinv, because mpred is still
  iProp. In the future, this will change, and mpred can become abstract, with
  own/inv/cinv as features of the logic, not specifically tied to iProp.
  TODO: this should be upstreamed in Iris---see cpp2v-core#185. *)

(* own *)
Definition own `{Σ : cpp_logic} `{!inG Σ A} : gname → A → mpred :=
  λ γ a, ⎡ own.own γ a ⎤%I.
(* TODO: I'll leave sealing for later MRs. *)
(* Local Definition own_def `{Σ : cpp_logic} `{!inG Σ A}
  : gname → A → mpred := own.own.
Local Definition own_aux : seal (@own_def). Proof. by eexists. Qed.
Definition own := own_aux.(unseal).
Local Definition own_eq : @own = @own_def := own_aux.(seal_eq). *)
Arguments own {_ Σ A _} γ a.
Instance: Params (@own) 5 := {}.

(* inv *)
Definition inv `{Σ : cpp_logic} `{!invG Σ}
  : namespace → mpred → mpred := 
  λ N P, ⎡ invariants.inv N (∀ i, P i) ⎤%I.
(* Local Definition inv_def `{Σ : cpp_logic} `{!invG Σ}
  : namespace → mpred → mpred := invariants.inv.
Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
Definition inv := inv_aux.(unseal).
Local Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq). *)
Arguments inv {_ Σ _} N P.
Instance: Params (@inv) 4 := {}.

(* cinv *)
Definition cinv_own `{Σ : cpp_logic} `{!invG Σ, !cinvG Σ}
  : gname → frac → mpred :=
  λ γ q, ⎡ cancelable_invariants.cinv_own γ q ⎤%I. 
Arguments cinv_own {_ Σ _ _ } γ a.
Instance: Params (@cinv_own) 5 := {}.

Definition cinv `{Σ : cpp_logic} `{!invG Σ, !cinvG Σ}
  : namespace → gname → mpred → mpred :=
  λ N γ P, ⎡ cancelable_invariants.cinv N γ (∀ i, P i) ⎤%I.
(* Local Definition cinv_def `{Σ : cpp_logic} `{!invG Σ, !cinvG Σ}
  : namespace → gname → mpred → mpred := cancelable_invariants.cinv.
Local Definition cinv_aux : seal (@cinv_def). Proof. by eexists. Qed.
Definition cinv := cinv_aux.(unseal).
Local Definition cinv_eq : @cinv = @cinv_def := cinv_aux.(seal_eq). *)
Arguments cinv {_ Σ _ _} N P.
Instance: Params (@cinv) 6 := {}.

(* the names of invariants *)
Definition iname : Set := namespace.

Local Ltac clear_objectively :=
  iNext; rewrite monPred_objectively_unfold; by iFrame.

(* TODO: more to be ported *)
Section own_properties.
  Context `{Σ : cpp_logic, !inG Σ A}.
  Implicit Type (a : A).

  Lemma own_alloc a : ✓ a → |-- |==> Exists γ, own γ a.
  Proof. intros. rewrite -embed_exist -embed_bupd -own.own_alloc; eauto. Qed.

  Lemma own_alloc_frame a P Q :
    ✓ a ->
    (∀ γ, P ** own γ a |-- Q) ->
    P |-- |==> Q.
  Proof.
    iIntros (VL HQ) "HP".
    iMod (own_alloc a) as (γ) "H"; first done.
    iModIntro. iApply HQ. by iFrame.
  Qed.

  Lemma own_op γ a1 a2 : own γ (a1 ⋅ a2) -|- own γ a1 ** own γ a2.
  Proof. by rewrite -embed_sep -own.own_op. Qed.
  Lemma own_mono γ a1 a2 : a2 ≼ a1 → own γ a1 |-- own γ a2.
  Proof. intros. by rewrite /own own.own_mono. Qed.

  #[global] Instance own_ne γ : NonExpansive (@own _ Σ A _ γ).
  Proof. solve_proper. Qed.
  #[global] Instance own_proper γ :
    Proper ((≡) ==> (⊣⊢)) (@own _ Σ A _ γ) := ne_proper _.

  #[global] Instance own_mono' γ : Proper (flip (≼) ==> (⊢)) (@own _ Σ A _ γ).
  Proof. intros ???. by rewrite /own own.own_mono'. Qed.
  #[global] Instance own_timeless γ a : Discrete a → Timeless (own γ a) := _.
  #[global] Instance own_core_persistent γ a : CoreId a → Persistent (own γ a) := _.

  (* TODO: overload uPred_cmra_valid as well *)
  Lemma own_valid γ a : own γ a |-- ⎡ ✓ a ⎤.
  Proof. by rewrite /own own.own_valid. Qed.
  Lemma own_valid_2 γ a1 a2 : own γ a1 -∗ own γ a2 -* ⎡ ✓ (a1 ⋅ a2) ⎤.
  Proof. by rewrite /own -embed_wand own.own_valid_2. Qed.
  Lemma own_valid_3 γ a1 a2 a3 :
    own γ a1 -∗ own γ a2 -∗ own γ a3 -* ⎡ ✓ (a1 ⋅ a2 ⋅ a3) ⎤.
  Proof. by rewrite /own -!embed_wand own.own_valid_3. Qed.
  Lemma own_valid_r γ a : own γ a |-- own γ a ** ⎡ ✓ a ⎤.
  Proof. by rewrite /own -embed_sep -own.own_valid_r. Qed.
  Lemma own_valid_l γ a : own γ a |-- ⎡ ✓ a ⎤** own γ a.
  Proof. by rewrite /own -embed_sep -own.own_valid_l. Qed.

  Lemma own_update γ a a' : a ~~> a' → own γ a |-- |==> own γ a'.
  Proof. intros. rewrite /own -embed_bupd -own.own_update; eauto. Qed.
  Lemma own_update_2 γ a1 a2 a' :
    a1 ⋅ a2 ~~> a' → own γ a1 |-- own γ a2 -* |==> own γ a'.
  Proof. intros. rewrite /own -embed_bupd -embed_wand -own.own_update_2; eauto. Qed.
  Lemma own_update_3 γ a1 a2 a3 a' :
    a1 ⋅ a2 ⋅ a3 ~~> a' → own γ a1 |-- own γ a2 -* own γ a3 -* |==> own γ a'.
  Proof. intros. rewrite /own -embed_bupd -!embed_wand -own.own_update_3; eauto. Qed.
End own_properties.

(* TODO: more to be ported *)
Section inv_properties.
  Context `{Σ : cpp_logic, !invG Σ}.
  Implicit Types (P Q : mpred) (γ : gname) (N : namespace) (E : coPset).

  Lemma inv_alloc' N E P :
    |> <obj> P |-- |={E}=> inv N P.
  Proof.
    rewrite /inv -embed_fupd -invariants.inv_alloc
            monPred_objectively_unfold -embed_later. eauto.
  Qed.
  Lemma inv_alloc N E P `{!Objective P}:
    |> P |-- |={E}=> inv N P.
  Proof. by rewrite -inv_alloc' -objective_objectively. Qed.

  #[global] Instance inv_contractive N : Contractive (inv N).
  Proof. rewrite /inv. solve_contractive. Qed.
  #[global] Instance inv_ne N : NonExpansive (inv N) := _.
  #[global] Instance inv_proper N : Proper (equiv ==> equiv) (inv N) := _.
  #[global] Instance inv_persistent N P : Persistent (inv N P) := _.
  #[global] Instance inv_affine N P : Affine (inv N P) := _.
End inv_properties.

Section cinv_properties.
  Context `{Σ : cpp_logic, !invG Σ, !cinvG Σ}.
  Implicit Types (P Q : mpred) (γ : gname) (N : namespace) (E : coPset).

  #[global] Instance cinv_own_timeless γ p : Timeless (cinv_own γ p) := _.
  #[global] Instance cinv_contractive N γ : Contractive (cinv N γ).
  Proof. rewrite /cinv. solve_contractive. Qed.
  #[global] Instance cinv_ne N γ : NonExpansive (cinv N γ) := _.
  #[global] Instance cinv_proper N γ : Proper ((≡) ==> (≡)) (cinv N γ) := _.
  #[global] Instance cinv_persistent N γ P : Persistent (cinv N γ P) := _.
  #[global] Instance cinv_affine N γ P : Affine (cinv N γ P) := _.
  #[global] Instance cinv_own_fractional γ : Fractional (cinv_own γ).
  Proof. intros ??. by rewrite -embed_sep -fractional. Qed.
  #[global] Instance cinv_own_as_fractional γ q :
    AsFractional (cinv_own γ q) (cinv_own γ) q.
  Proof. constructor; eauto. apply _. Qed.


  Lemma cinv_alloc' E N P :
    |> <obj> P |-- |={E}=> Exists γ, cinv N γ P ** cinv_own γ 1.
  Proof.
    rewrite /cinv. setoid_rewrite <-embed_sep. setoid_rewrite <-embed_exist.
    rewrite -embed_fupd -cancelable_invariants.cinv_alloc
            monPred_objectively_unfold -embed_later. eauto.
  Qed.
  Lemma cinv_alloc E N P `{!Objective P} :
    |> P |-- |={E}=> Exists γ, cinv N γ P ** cinv_own γ 1.
  Proof. by rewrite -cinv_alloc' -objective_objectively. Qed.

  Lemma cinv_cancel' E N γ P :
    ↑N ⊆ E →
    cinv N γ P |-- cinv_own γ 1 -* |={E}=> |> <obj> P.
  Proof.
    intros.
    by rewrite monPred_objectively_unfold -embed_later -embed_fupd -embed_wand
               -cancelable_invariants.cinv_cancel.
  Qed.

  Lemma cinv_cancel E N γ P :
    ↑N ⊆ E →
    cinv N γ P |-- cinv_own γ 1 -* |={E}=> |> P.
  Proof. intros. by rewrite cinv_cancel' // monPred_objectively_elim. Qed.

  Lemma cinv_alloc_cofinite' (G: gset gname) E N :
    |-- |={E}=> Exists γ, ⌜ γ ∉ G ⌝ ** cinv_own γ 1%Qp **
                          ∀ P, |> <obj> P ={E}=∗ cinv N γ P.
  Proof.
    rewrite /cinv monPred_objectively_unfold.
    iMod (cancelable_invariants.cinv_alloc_cofinite G E N)
      as (γ) "(NIn & Inv & New)".
    iIntros "!>". iExists γ. rewrite embed_pure. iFrame.
    iIntros (P) "P".
    rewrite embed_forall. setoid_rewrite embed_wand.
    setoid_rewrite embed_fupd. setoid_rewrite embed_later.
    by iApply ("New" with "P").
  Qed.

  Lemma cinv_alloc_cofinite (G: gset gname) E N :
    |-- |={E}=> Exists γ, ⌜ γ ∉ G ⌝ ** cinv_own γ 1%Qp **
                          ∀ P, ⌜ Objective P ⌝ → |> P ={E}=∗ cinv N γ P.
  Proof.
    iMod (cinv_alloc_cofinite' G E N) as (γ) "(NIn & Inv & New)".
    iIntros "!>". iExists γ. iFrame. iIntros (P OB).
    iSpecialize ("New" $! P). by rewrite -objective_objectively.
  Qed.

  (* Stronger allocation rule: stronger constraints on γ can be picked.
    Also see cinv_alloc_strong_open, the invariant can be allocated but
    establishing its content can be delayed. It can be added when needed. *)
  Lemma cinv_alloc_strong' (I : gname → Prop) E N :
    pred_infinite I →
    |-- |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P, |> <obj> P ={E}=∗ cinv N γ P.
  Proof.
    intros IN.
    rewrite /cinv monPred_objectively_unfold.
    iMod (cancelable_invariants.cinv_alloc_strong _ E N IN)
      as (γ) "(NIn & Inv & New)".
    iIntros "!>". iExists γ. rewrite embed_pure. iFrame.
    iIntros (P) "P".
    rewrite embed_forall. setoid_rewrite embed_wand.
    setoid_rewrite embed_fupd. setoid_rewrite embed_later.
    by iApply ("New" with "P").
  Qed.
  Lemma cinv_alloc_strong (I : gname → Prop) E N :
    pred_infinite I →
    |-- |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗
                      ∀ P, ⌜ Objective P ⌝ → |> P ={E}=∗ cinv N γ P.
  Proof.
    intros IN.
    iMod (cinv_alloc_strong' _ E N IN) as (γ) "(NIn & Inv & New)".
    iIntros "!>". iExists γ. iFrame. iIntros (P OB).
    iSpecialize ("New" $! P). by rewrite -objective_objectively.
  Qed.

  Corollary cinv_alloc_ghost_named_inv' E N (I : gname → mpred) :
    (∀ γ , |> <obj> I γ) |--
    |={E}=> Exists γ, cinv N γ (I γ) ** cinv_own γ 1.
  Proof.
    iIntros "I".
    iMod (cinv_alloc_cofinite' empty E N) as (γ ?) "[HO HI]".
    iSpecialize ("I" $! γ).
    iMod ("HI" $! (I γ) with "[$I]") as "HI".
    iIntros "!>". eauto with iFrame.
  Qed.

  Corollary cinv_alloc_ghost_named_inv E N (I : gname → mpred)
    `{!∀ γ, Objective (I γ)} :
    (∀ γ , |> I γ) |--
    |={E}=> Exists γ, cinv N γ (I γ) ** cinv_own γ 1.
  Proof.
    rewrite -cinv_alloc_ghost_named_inv'.
    iIntros "P" (γ). iSpecialize ("P" $! γ). by rewrite -objective_objectively.
  Qed.

  Lemma cinv_acc_strong' E N γ p P :
    ↑N ⊆ E →
    cinv N γ P |-- (cinv_own γ p ={E,E∖↑N}=∗
                          (|> <obj> P ** cinv_own γ p **
                          (Forall (E' : coPset),
                            ((|> <obj> P \\// cinv_own γ 1) ={E',↑N ∪ E'}=∗ True)))).
  Proof.
    iIntros (SUB) "Inv own". rewrite monPred_objectively_unfold.
    iMod (cancelable_invariants.cinv_acc_strong with "Inv own")
      as "(P & own & Close)"; first done.
    iIntros "!>". rewrite embed_later. iFrame. iIntros (E') "P".
    iMod ("Close" with "[P]"); last done. rewrite /cinv embed_or -embed_later.
    by iFrame.
  Qed.

  Lemma cinv_acc_strong E N γ p P `{!Objective P}:
    ↑N ⊆ E →
    cinv N γ P |-- (cinv_own γ p ={E,E∖↑N}=∗
                          (|> P ** cinv_own γ p **
                          (Forall (E' : coPset),
                            ((|> P \\// cinv_own γ 1) ={E',↑N ∪ E'}=∗ True)))).
  Proof.
    iIntros (SUB) "Inv own".
    iMod (cinv_acc_strong' with "Inv own") as "(P & $ & Close)"; first done.
    iIntros "!>". iSplitL "P"; first by rewrite monPred_objectively_elim.
    iIntros (E'). iSpecialize ("Close" $! E'). by rewrite -objective_objectively.
  Qed.
End cinv_properties.
