(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)

(** T-local invariants, which are only useable within the same local state T,
    and thus can be used to shared T-dependent resources *)
From iris.bi Require Import bi monpred.
From iris.proofmode Require Import tactics.

Require Import bedrock.lang.bi.mlens.
Require Import bedrock.lang.bi.tls_modalities.
Require Import bedrock.lang.bi.invariants.
Require Import bedrock.lang.bi.cancelable_invariants.

(* TODO: write a README for all this. *)
Class MLensStable {I J} (L: MLens I J) :=
  mlens_stable i i' : i ⊑ i' → i'.^L = i.^L.
Arguments MLensStable {_ _} _.
Arguments mlens_stable {_ _} _ {_}.
#[global] Hint Mode MLensStable ! ! + : typeclass_instances.
Instance: Params (@mlens_stable) 2 := {}.

Section local_inv.
  Context {I J : biIndex} `{!invG Σ} (L: MLens I J).
  Notation monPred := (monPred I (iPropI Σ)).
  Implicit Types (i j : I) (γ : gname) (P Q R : monPred).

  #[local] Definition own_inv (N : namespace) P : monPred :=
    ⌜ LocalWith L P ∧ MLensStable L ⌝ ∧
    ∃ i, monPred_in i ∧ (* >> this says the current local state is at least i *)
      ⎡ lib.invariants.inv N (P i) ⎤.

  #[local] Lemma own_inv_acc E N P :
    ↑N ⊆ E → own_inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    intros SUB. constructor => j.
    iDestruct 1 as ([LW ST] i Le) "INV".
    iInv N as "P" "Close".
    iIntros "!>". iFrame "P".
    iIntros (i' Lei) "P".
    iMod ("Close" with "[P]"); last done.
    rewrite (local_with L _ i' i) // (mlens_stable L i) //. by etrans.
  Qed.

  #[local] Lemma own_inv_alloc N E P {ST: MLensStable L} {LW: LocalWith L P} :
    ▷ P ={E}=∗ own_inv N P.
  Proof.
    iIntros "P". iDestruct (monPred_in_intro with "P") as (i) "[In P]".
    iMod (lib.invariants.inv_alloc _ _ (P i) with "[P]") as "P".
    - rewrite monPred_at_later. by iFrame.
    - iIntros "!>". iSplit; [done|]. iExists i. by iFrame.
  Qed.

  (* This does not imply [own_inv_alloc] due to the extra assumption [↑N ⊆ E]. *)
  #[local] Lemma own_inv_alloc_open N E P {ST: MLensStable L} {LW: LocalWith L P} :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> own_inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    intros Sub.
    iDestruct (monPred_in_intro True with "[//]") as (i) "[Ini _]".
    iMod (lib.invariants.inv_alloc_open N E (P i)) as "[Inv Close]"; [done|].
    iIntros "!>". iSplit; first iSplit; [done|..].
    - iExists i. by iFrame "#∗".
    - iIntros "P". iMod ("Close" with "[P]"); last done.
      iCombine "Ini" "P" as "Pi".
      iDestruct (monPred_in_intro with "Pi") as (j) "(_ & % & P)".
      rewrite (local_with L _ j i) // (mlens_stable L i) //.
  Qed.

  #[local] Lemma own_inv_to_inv M P : own_inv M P -∗ inv M P.
  Proof.
    iIntros "#I". rewrite inv_eq. iIntros (E H).
    iPoseProof (own_inv_acc with "I") as "H"; eauto.
  Qed.

  Lemma inv_alloc N E P `{!MLensStable L} `{!LocalWith L P} : ▷ P ={E}=∗ inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iApply (own_inv_alloc N E with "HP").
  Qed.

  Lemma inv_alloc_open N E P `{!MLensStable L} `{!LocalWith L P} :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?). iMod own_inv_alloc_open as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.
End local_inv.


(* Allocation rules for monPred that are tied specifically to iProp. *)
Section local_cinv.
  Context {K J : biIndex} `{!invG Σ, !cinvG Σ} (L : MLens K J).

  Notation monPred := (monPred K (iPropI Σ)).
  Notation monPredI := (monPredI K (iPropI Σ)).

  Implicit Types (i j : K) (γ : gname) (P Q R : monPred).

  (* some re-exporting of embedding properties *)
  #[global] Instance monPred_own_local_with `{!inG Σ A} γ (a : A) :
    LocalWith L (own γ a).
  Proof. rewrite has_own_monpred_eq. apply _. Qed.

  Typeclasses Transparent cinv_own cinv.
  (*** Allocation rules. *)
  (** The "strong" variants permit any infinite [I], and choosing [P] is delayed
  until after [γ] was chosen.*)
  Lemma cinv_alloc_strong (I : gname → Prop) E N `{!MLensStable L} :
    pred_infinite I →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗
                    ∀ P, ⌜ LocalWith L P ⌝ → ▷ P ={E}=∗ cinv N γ P.
  Proof.
    iIntros (?). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ} {$Hfresh}" (P LW) "HP".
    iMod (inv_alloc L N _ (P ∨ cinv_own γ 1) with "[HP]"); eauto.
  Qed.

  (** The "open" variants create the invariant in the open state, and delay
  having to prove [P].
  These do not imply the other variants because of the extra assumption [↑N ⊆ E]. *)
  Lemma cinv_alloc_strong_open (I : gname → Prop) E N `{!MLensStable L} :
    pred_infinite I →
    ↑N ⊆ E →
    ⊢ |={E}=> ∃ γ, ⌜ I γ ⌝ ∗ cinv_own γ 1 ∗ ∀ P, ⌜ LocalWith L P ⌝ →
      |={E,E∖↑N}=> cinv N γ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (??). iMod (own_alloc_strong 1%Qp I) as (γ) "[Hfresh Hγ]"; [done|done|].
    iExists γ. iIntros "!> {$Hγ $Hfresh}" (P LW).
    iMod (inv_alloc_open L N _ (P ∨ cinv_own γ 1)) as "[Hinv Hclose]"; first by eauto.
    iIntros "!>". iFrame. iIntros "HP". iApply "Hclose". iLeft. done.
  Qed.

  Lemma cinv_alloc_cofinite (G : gset gname) E N `{!MLensStable L} :
    ⊢ |={E}=> ∃ γ, ⌜ γ ∉ G ⌝ ∗ cinv_own γ 1 ∗
                    ∀ P, ⌜ LocalWith L P ⌝ → ▷ P ={E}=∗ cinv N γ P.
  Proof.
    apply : cinv_alloc_strong. apply (pred_infinite_set (C:=gset gname))=> E'.
    exists (fresh (G ∪ E')). apply not_elem_of_union, is_fresh.
  Qed.

  Lemma cinv_alloc E N P `{!MLensStable L} `{!LocalWith L P} :
    ▷ P ={E}=∗ ∃ γ, cinv N γ P ∗ cinv_own γ 1.
  Proof.
    iIntros "HP". iMod (cinv_alloc_cofinite ∅ E N) as (γ _) "[Hγ Halloc]".
    iExists γ. iFrame "Hγ". by iApply "Halloc".
  Qed.

  Lemma cinv_alloc_open E N P `{!MLensStable L} `{LW: LocalWith _ _ _ L P} :
    ↑N ⊆ E → ⊢ |={E,E∖↑N}=> ∃ γ, cinv N γ P ∗ cinv_own γ 1 ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    iIntros (?). iMod (cinv_alloc_strong_open (λ _, True)) as (γ) "(_ & Htok & Hmake)"; [|done|].
    { apply pred_infinite_True. }
    iMod ("Hmake" $! P LW) as "[Hinv Hclose]". iIntros "!>". iExists γ. iFrame.
  Qed.
End local_cinv.

Typeclasses Opaque cinv_own cinv.
