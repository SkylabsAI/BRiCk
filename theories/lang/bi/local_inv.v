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