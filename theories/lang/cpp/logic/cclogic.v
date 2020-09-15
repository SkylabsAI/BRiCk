(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Coq.ssr.ssrbool.

From Coq.Classes Require Import
     RelationClasses Morphisms DecidableClass.

From iris.bi Require Import lib.fractional monpred.
From iris.base_logic.lib Require Import
      fancy_updates invariants cancelable_invariants own wsat.
Import invG.
From iris.algebra Require Import excl auth.

From iris.proofmode Require Import tactics.

Require Import bedrock.ChargeCompat.
Require Import bedrock.lang.cpp.ast.
From bedrock.lang.cpp Require Import
     logic.pred.

Bind Scope string_scope with namespace.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Section with_Σ.
  Context `{Σ : cpp_logic ti}.

  Section with_own.
    Context `{!inG Σ A}.

    Definition own (γ : gname) (a : A) : mpred :=  ⎡ own.own γ a ⎤.

    Lemma own_alloc : forall (a : A), ✓ a → |-- |==> ∃ γ, own γ a.
    Proof.
      intros a Va. iStartProof. iMod (own_alloc a Va) as (γ) "?". eauto.
    Qed.

    Lemma own_alloc_frame (R : A) : forall P Q,
        ✓ R ->
        (forall (γ : gname), P ** own γ R |-- Q) ->
        P |-- |==> Q.
    Proof.
      intros ?? HR HQ.
      iIntros "HP".
      iMod (own_alloc R) as (γ) "H"; first done.
      iModIntro.
      iApply HQ.
      iFrame.
    Qed.

  End with_own.

  Example viewshift_example (P Q : mpred) (N : namespace) :
    (P -* |={ ⊤ ∖ ↑N, ⊤  }=> Q) ** (|={⊤, ⊤ ∖ ↑N}=> P)%I |-- |={⊤}=> Q.
  Proof.
    (* Introduce hypotheses into context by destructing separation conjunct *)
    iIntros "[HPQ HP]".
    (* Construct hypothesis granularity *)
    iMod "HP".
    (* Resolve second shift *)
    iApply "HPQ".
    (* Resolve first shift *)
    iApply "HP".
  Qed.

  Local Ltac clear_objectively :=
    iNext; rewrite monPred_objectively_unfold; by iFrame.

  Section with_invG.
    Context `{!invG Σ}.

    (* the names of invariants *)
    Definition iname : Set := namespace.

    Bind Scope string_scope with iname.

    (* named invariants *)
    (* mpred version of [inv]: s/inv/Inv;s/iProp Σ/mpred *)
    Definition Inv : namespace → mpred → mpred := λ N P, ⎡ inv N (∀ i, P i) ⎤%I.

    Lemma Inv_alloc N P : |> <obj> P |-- (|={⊤}=> Inv N P)%I.
    Proof.
      intros. iIntros "I".
      iMod (inv_alloc with "[I]") as "$"; last done.
      clear_objectively.
    Qed.

    Lemma Inv_acc E N P :
      ↑N ⊆ E → Inv N P |-- |={E,E∖↑N}=> |> <obj> P ∗ (|> <obj> P ={E∖↑N,E}=∗ emp).
    Proof.
      iIntros (SN) "I".
      iMod (inv_acc with "I") as "[I C]"; first done.
      iModIntro. iSplitL "I"; first clear_objectively.
      iIntros "I". iMod ("C" with "[I]"); last done.
      clear_objectively.
    Qed.

    Global Instance Inv_contractive N : Contractive (Inv N).
    Proof. solve_contractive. Qed.

    Global Instance Inv_ne N : NonExpansive (Inv N) := _.

    Global Instance Inv_proper N : Proper (equiv ==> equiv) (Inv N) := _.

    Global Instance Inv_persistent : Persistent (Inv n P) := _.

    Global Instance Inv_affine : Affine (Inv n P) := _.

    Global Instance into_acc_Inv N P E:
    IntoAcc (X := unit) (Inv N P)
            (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
            (λ _ : (), (▷ <obj> P)%I) (λ _ : (), (▷ <obj> P)%I) (λ _ : (), None).
    Proof.
      rewrite /IntoAcc /accessor bi.exist_unit /=.
      iIntros (?) "Hinv _".
      by iApply (Inv_acc with "Hinv").
    Qed.
  End with_invG.

  Section with_cinvG.
    Context `{!cinvG Σ}.
    (* mpred version of [cinv]: s/cinv/TInv;s/iProp Σ/mpred *)
    Definition TInv : namespace → gname → mpred → mpred
      := λ N γ P, ⎡ cinv N γ (∀ i, P i) ⎤%I.

    Definition TInv_own : gname → frac → mpred
      := λ γ q, ⎡ cinv_own γ q ⎤%I.

    (* a stronger invariant allocation lemma. This allows one to:
      - pick the ghost name γ to be outside of a set G (γ ∉ G)
      - delay picking the invariant I until γ is allocated, so that I can
        depend on γ. Notably, one can put the invariant token TInv_own γ q
        inside the invariant I. *)
    Lemma TInv_alloc_cofinite : forall (G: gset gname) M N,
      |-- (|={M}=> Exists γ, ⌜ γ ∉ G ⌝ ** TInv_own γ 1%Qp **
                            ∀ I, ▷ <obj> I ={M}=∗ TInv N γ I)%I.
    Proof.
      intros.
      iMod (cinv_alloc_cofinite G M N) as (γ Fγ) "[O FI]".
      iModIntro. iExists γ. iFrame (Fγ) "O".
      iIntros (I) "I". iMod ("FI" with "[I]") as "$"; last done.
      clear_objectively.
    Qed.

    (* Even stronger: stronger constraints on γ can be picked
      Also see cinv_alloc_strong_open, the invariant can be allocated but
      establishing its content can be delayed. It can be added when needed. *)
    Lemma TInv_alloc_strong : forall (F : gname → Prop) M N,
      pred_infinite F →
      |-- |={M}=> ∃ γ, ⌜ F γ ⌝ ∗ TInv_own γ 1 ∗ ∀ I, ▷ <obj> I ={M}=∗ TInv N γ I.
    Proof.
      intros F M N PF.
      iMod (cinv_alloc_strong F M N PF) as (γ Fγ) "[O FI]".
      iModIntro. iExists γ. iFrame (Fγ) "O".
      iIntros (I) "I". iMod ("FI" with "[I]") as "$"; last done.
      clear_objectively.
    Qed.

    Corollary TInv_alloc_ghost_named_inv : forall M N I,
      (∀ γ : gname, <obj> I γ) |--
      (|={M}=> Exists γ, TInv N γ (I γ) ** TInv_own γ 1%Qp )%I.
    Proof.
      intros. iIntros "I".
      iMod (TInv_alloc_cofinite empty M N) as (γ ?) "[HO HI]".
      iSpecialize ("I" $! γ).
      iMod ("HI" $! (I γ) with "[$I]") as "HI".
      iIntros "!>". eauto with iFrame.
    Qed.

    Lemma TInv_alloc : forall M N I,
      |> <obj> I |-- (|={M}=> Exists γ, TInv N γ I ** TInv_own γ 1%Qp)%I.
    Proof.
      intros. iIntros "I".
      iMod (cinv_alloc with "[I]") as (γ) "[I O]"; last by eauto.
      clear_objectively.
    Qed.

    Lemma TInv_acc E N γ (q: frac) P :
      ↑N ⊆ E →
      TInv N γ P |-- TInv_own γ q -*
        |={E,E∖↑N}=> |> <obj> P ∗ TInv_own γ q ∗ (|> <obj> P ={E∖↑N,E}=∗ emp).
    Proof.
      iIntros (?) "#Hinv Hγ".
      iMod (cinv_acc with "Hinv Hγ") as "(I & $ & H)"; first done.
      iIntros "!>". iSplitL "I"; first clear_objectively.
      iIntros "I". iMod ("H" with "[I]"); last done.
      clear_objectively.
    Qed.

    Global Instance TInv_own_timeless γ q : Timeless (TInv_own γ q) := _.

    Global Instance TInv_contractive N γ : Contractive (TInv N γ).
    Proof. solve_contractive. Qed.
    Global Instance TInv_ne N γ : NonExpansive (TInv N γ) := _.
    Global Instance TInv_proper N γ : Proper ((≡) ==> (≡)) (TInv N γ) := _.

    Global Instance TInv_persistent : Persistent (TInv Ns γ P) := _.

    Global Instance TInv_affine : Affine (TInv Ns γ P) := _.

    Global Instance TInv_own_fractional γ : Fractional (TInv_own γ).
    Proof. intros ??. by rewrite -embed_sep -fractional. Qed.
    Global Instance TInv_own_as_fractional γ q :
      AsFractional (TInv_own γ q) (TInv_own γ) q.
    Proof. split; [done|apply _]. Qed.

    Lemma TInv_cancel M N γ I :
      ↑N ⊆ M ->
      TInv N γ I |-- TInv_own γ 1%Qp -* (|={M}=> |> <obj> I)%I.
    Proof.
      iIntros (SN) "TI O".
      iMod (cinv_cancel with "[$TI] [$O]") as "I"; first done.
      iModIntro. clear_objectively.
    Qed.

    #[deprecated(since="20200824", note="Use TInv_cancel instead")]
    Lemma TInv_delete M N γ I :
      ↑N ⊆ M ->
      TInv N γ I ** TInv_own γ 1%Qp |-- (|={M}=> |> <obj> I)%I.
    Proof. intros. iIntros "[#? ?]". iApply TInv_cancel; eauto. Qed.

(*
    Lemma cinv_open_stronger E N γ p P :
      ↑N ⊆ E →
      cinv N γ P ⊢ (cinv_own γ p ={E,E∖↑N}=∗
                    ((|>P) ** cinv_own γ p ** (Forall (E' : coPset), ((|>(P ∨ cinv_own γ 1)) ={E',↑N ∪ E'}=∗ True)))).
    Proof.
      iIntros (?) "Hinv Hown".
      unfold cinv. (* iDestruct "Hinv" as (P') "[#HP' Hinv]". *)
      iPoseProof (inv_acc (↑ N) N _ with "Hinv") as "H"; first done.
      rewrite difference_diag_L.
      iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
      rewrite left_id_L -union_difference_L //. iMod "H" as "[[HP | >HP] H]".
      - iModIntro. iFrame. iDestruct ("HP'" with "HP") as "HP". iFrame. iModIntro.
        iIntros (E') "HP".
        iPoseProof (fupd_mask_frame_r _ _ E' with "(H [HP])") as "H"; first set_solver.
        { iDestruct "HP" as "[HP | >Hown]".
          iLeft. by iApply "HP'".
          eauto.
        }
          by rewrite left_id_L.
      - iDestruct (cinv_own_1_l with "HP Hown") as %[].
    Qed.
*)

    Lemma TInv_acc_strong E N γ p P :
      ↑N ⊆ E →
      TInv N γ P |-- (TInv_own γ p ={E,E∖↑N}=∗
                            ((|> <obj> P) ** TInv_own γ p **
                            (Forall (E' : coPset),
                              ((|> <obj> P ∨ TInv_own γ 1) ={E',↑N ∪ E'}=∗ True))))%I.
    Proof.
      iIntros (SN) "TI O".
      iMod (cinv_acc_strong with "[$TI] [$O]") as "(I & $ & FI)"; first done.
      iModIntro. iSplitL "I"; first clear_objectively.
      iIntros (E') "PO". iMod ("FI" with "[PO]"); last done.
      iDestruct "PO" as "[P|O]"; last (iRight; by iFrame).
      iLeft. clear_objectively.
    Qed.

    (* for proofmode's iInv *)
    Global Instance into_acc_TInv E N γ P q :
      IntoAcc (X:=unit) (TInv N γ P)
              (↑N ⊆ E) (TInv_own γ q) (fupd E (E∖↑N)) (fupd (E∖↑N) E)
              (λ _, |> <obj> P ∗ TInv_own γ q)%I (λ _, |> <obj> P)%I (λ _, None)%I.
    Proof.
      rewrite /IntoAcc /accessor bi.exist_unit -assoc.
      iIntros (?) "#Hinv Hown".
      by iApply (TInv_acc with "Hinv Hown").
    Qed.
  End with_cinvG.
End with_Σ.

#[deprecated(since="20200824", note="Use Inv_alloc instead")]
Notation Inv_new := Inv_alloc (only parsing).

#[deprecated(since="20200824", note="Use TInv_alloc instead")]
Notation TInv_new := TInv_alloc (only parsing).

#[deprecated(since="20200824", note="Use TInv_acc_strong instead")]
Notation Tinv_open_strong := TInv_acc_strong (only parsing).
