(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(* TODO: LICENSE for Iris. *)

(** Extraction of invariants that doesn't depend on iProp. *)

Require Import iris.bi.monpred.
Require Import iris.algebra.lib.excl_auth.
Require Import iris.base_logic.lib.invariants.

From iris.proofmode Require Import tactics monpred.

Require Export bedrock.lang.bi.weakly_objective.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Implicit Types (N : namespace).

Section defs.
  Context `{!BiFUpd PROP}.

  (* Duplicates from Iris, but more general. *)
  Definition inv_def N (P : PROP) : PROP :=
    (□ ∀ E : coPset, ⌜↑N ⊆ E⌝ → |={E,E ∖ ↑N}=> ▷ P ∗ (▷ P ={E ∖ ↑N,E}=∗ True))%I.
  Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
  Definition inv := inv_aux.(unseal).
  Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).

  Section instances.
    Context `{CON: BiLaterContractive PROP}.
    Global Instance inv_contractive N : Contractive (inv N).
    Proof using CON. rewrite inv_eq. solve_contractive. Qed.

    Global Instance inv_ne `{BiLaterContractive PROP} N : NonExpansive (inv N).
    Proof using CON. apply contractive_ne, _. Qed.

    Global Instance inv_proper N : Proper (equiv ==> equiv) (inv N).
    Proof using CON. apply ne_proper, _. Qed.
  End instances.

  Global Instance inv_persistent N P : Persistent (inv N P).
  Proof. rewrite inv_eq. apply _. Qed.
  Global Instance inv_affine N P : Affine (inv N P).
  Proof. rewrite inv_eq. apply _. Qed.
End defs.

Arguments inv {_ _} N P%I.
Instance : Params (@inv) 3 := {}.

Section inv_properties.
Context `{!BiFUpd PROP}.

Implicit Types (P Q : PROP) (E : coPset).

(* Duplicates from Iris, but do not tie to iProp *)
(* These statements (and probably proofs) are the same, except where required
for linearity. *)
Lemma inv_alter N P Q :
  inv N P -∗ □ ▷ (P -∗ Q ∗ (Q -∗ P)) -∗ inv N Q.
Proof.
  rewrite inv_eq. iIntros "#HI #HPQ !>" (E SUB).
  iMod ("HI" $! E SUB) as "[HP Hclose]".
  iDestruct ("HPQ" with "HP") as "[$ HQP]".
  iIntros "!> HQ". iApply "Hclose". iApply "HQP". done.
Qed.

Lemma inv_iff N P Q : inv N P -∗ □ ▷ (P ∗-∗ Q) -∗ inv N Q.
Proof.
  iIntros "#HI #HPQ". iApply (inv_alter with "HI").
  iIntros "!> !> HP". iSplitL "HP".
  - by iApply "HPQ".
  - iIntros "HQ". by iApply "HPQ".
Qed.

Lemma inv_acc E N P :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
Proof.
  rewrite inv_eq /inv_def; iIntros (?) "HI". by iApply ("HI" $! E with "[%//]").
Qed.

Lemma inv_combine N1 N2 N P Q :
  N1 ## N2 →
  ↑N1 ∪ ↑N2 ⊆@{coPset} ↑N →
  inv N1 P -∗ inv N2 Q -∗ inv N (P ∗ Q).
Proof.
  rewrite inv_eq. iIntros (??) "#HinvP #HinvQ !>"; iIntros (E ?).
  iMod ("HinvP" with "[%]") as "[$ HcloseP]"; first set_solver.
  iMod ("HinvQ" with "[%]") as "[$ HcloseQ]"; first set_solver.
  iMod (fupd_intro_mask' _ (E ∖ ↑N)) as "Hclose"; first set_solver.
  iIntros "!> [HP HQ]".
  iMod "Hclose" as "_". iMod ("HcloseQ" with "HQ") as "?". by iMod ("HcloseP" with "HP").
Qed.

Lemma inv_combine_dup_l N P Q :
  □ (P -∗ P ∗ P) -∗
  inv N P -∗ inv N Q -∗ inv N (P ∗ Q).
Proof.
  rewrite inv_eq. iIntros "#HPdup #HinvP #HinvQ !>" (E SUB).
  iMod ("HinvP" with "[%//]") as "[HP HcloseP]".
  iDestruct ("HPdup" with "HP") as "[$ HP]".
  iMod ("HcloseP" with "HP") as "?".
  iMod ("HinvQ" with "[%//]") as "[$ HcloseQ]".
  iIntros "!> [HP HQ]". by iMod ("HcloseQ" with "HQ").
Qed.

(** ** Proof mode integration *)
Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

Global Instance into_acc_inv N P E:
  IntoAcc (X := unit) (inv N P)
          (↑N ⊆ E) emp (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
          (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), Some True%I).
Proof.
  rewrite inv_eq /IntoAcc /accessor bi.exist_unit.
  iIntros (?) "Hinv _". iMod ("Hinv" $! E with "[%//]") as "[$ Close]".
  iIntros "!> P /=". by iMod ("Close" with "P") as "?".
Qed.

(** ** Derived properties *)
Lemma inv_acc_strong E N P :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ True.
Proof.
  iIntros (?) "Hinv".
  iPoseProof (inv_acc (↑ N) N with "Hinv") as "H"; first done.
  rewrite difference_diag_L.
  iPoseProof (fupd_mask_frame_r _ _ (E ∖ ↑ N) with "H") as "H"; first set_solver.
  rewrite left_id_L -union_difference_L //. iMod "H" as "[$ H]"; iModIntro.
  iIntros (E') "HP".
  iPoseProof (fupd_mask_frame_r _ _ E' with "(H HP)") as "H"; first set_solver.
  by rewrite left_id_L.
Qed.

Lemma inv_acc_timeless E N P `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
Proof.
  iIntros (?) "Hinv". iMod (inv_acc with "Hinv") as "[>HP Hclose]"; auto.
  iIntros "!> {$HP} HP". iApply "Hclose"; auto.
Qed.

Lemma inv_split_l N P Q : inv N (P ∗ Q) -∗ inv N P.
Proof.
  iIntros "#HI". iApply inv_alter; eauto.
  iIntros "!> !> [$ $] $".
Qed.
Lemma inv_split_r N P Q : inv N (P ∗ Q) -∗ inv N Q.
Proof.
  iIntros "#HI". iApply inv_alter; eauto.
  iIntros "!> !> [$ $] $".
Qed.
Lemma inv_split N P Q : inv N (P ∗ Q) -∗ inv N P ∗ inv N Q.
Proof.
  iIntros "#H".
  iPoseProof (inv_split_l with "H") as "$".
  iPoseProof (inv_split_r with "H") as "$".
Qed.
End inv_properties.

(*** Invariants for monPred **)

(* Allocations are not general for arbitrary BI. This one here is developed for
  monPred, basing on iProp. *)
Section allocation.
  Context {I : biIndex} `{!invG Σ}.
  Notation monPred := (monPred I (iPropI Σ)).
  Implicit Types (i j : I) (γ : gname) (P Q R : monPred).

  (** ** Internal model of invariants *)
  #[local] Definition own_inv (N : namespace) P : monPred :=
    ⌜WeaklyObjective P⌝ ∧
    ∃ i, monPred_in i ∧ (* >> this says the current local state is at least i *)
      ⎡ lib.invariants.inv N (P i) ⎤.

  #[local] Lemma own_inv_acc E N P :
    ↑N ⊆ E → own_inv N P ={E,E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N,E}=∗ True).
  Proof.
    intros SUB. constructor => j.
    iDestruct 1 as (WK i Le) "INV".
    iInv N as "P" "Close".
    iIntros "!>". iFrame "P".
    iIntros (i' Lei) "P".
    iMod ("Close" with "[P]"); last done.
    rewrite weakly_objective. iFrame. by etrans.
  Qed.

  #[local] Lemma own_inv_alloc N E P {WK: WeaklyObjective P} :
    ▷ P ={E}=∗ own_inv N P.
  Proof.
    iIntros "P". iDestruct (monPred_in_intro with "P") as (i) "[In P]".
    iFrame (WK). iExists i. iFrame "In".
    iMod (lib.invariants.inv_alloc _ _ (P i) with "[P]") as "$"; last done.
    rewrite monPred_at_later. by iFrame.
  Qed.

  (* This does not imply [own_inv_alloc] due to the extra assumption [↑N ⊆ E]. *)
  #[local] Lemma own_inv_alloc_open N E P {WK: WeaklyObjective P} :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> own_inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    intros Sub.
    iDestruct (monPred_in_intro True with "[//]") as (i) "[Ini _]".
    iMod (lib.invariants.inv_alloc_open N E (P i)) as "[Inv Close]"; [done|].
    iIntros "!>". iFrame (WK). iSplit.
    - iExists i. by iFrame "#∗".
    - iIntros "P". iMod ("Close" with "[P]"); last done.
      iCombine "Ini" "P" as "Pi".
      iDestruct (monPred_in_intro with "Pi") as (j) "(_ & % & P)".
      by rewrite weakly_objective.
  Qed.

  #[local] Lemma own_inv_to_inv M P: own_inv M P -∗ inv M P.
  Proof.
    iIntros "#I". rewrite inv_eq. iIntros (E H).
    iPoseProof (own_inv_acc with "I") as "H"; eauto.
  Qed.

  Lemma inv_alloc N E P `{!WeaklyObjective P} : ▷ P ={E}=∗ inv N P.
  Proof.
    iIntros "HP". iApply own_inv_to_inv.
    iApply (own_inv_alloc N E with "HP").
  Qed.

  Lemma inv_alloc_open N E P `{!WeaklyObjective P} :
    ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
  Proof.
    iIntros (?). iMod own_inv_alloc_open as "[HI $]"; first done.
    iApply own_inv_to_inv. done.
  Qed.
End allocation.

(* A proof that inv is objective if its content is objective. *)
Section minv.
  Context {I : biIndex} `{!BiFUpd PROP}.

  Lemma inv_obj_obj_inv N (P : monPred I PROP) `{Objective I PROP P} :
    inv N P ⊣⊢ <obj> inv N P.
  Proof.
    constructor => i. rewrite inv_eq /inv_def monPred_at_objectively. iSplit.
    - iIntros "#INV" (j) "!>". iIntros (E j1 Lej1 NE).
      iMod ("INV" $! E NE) as "[P Close]". iClear "INV".
      iIntros "!>". rewrite objective_at. iFrame "P".
      iIntros (??) "P".
      iMod ("Close" with "[P]"); last done. by rewrite objective_at.
    - iIntros "#INV !>" (E ?? NE).
      iSpecialize ("INV" $! i). iDestruct "INV" as "#INV".
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". rewrite objective_at. iFrame "P".
      iIntros (??) "P".
      iMod ("Close" with "[P]"); last done. by rewrite objective_at.
  Qed.

  Lemma inv_obj_obj_inv' N (P : monPred I PROP) :
    inv N (<obj> P) ⊣⊢ <obj> inv N (<obj> P).
  Proof. apply inv_obj_obj_inv, _. Qed.
End minv.

(* This establish the equivalence between lib.invariants.inv and inv for monPred. *)
Section oinv.
  Context {I : biIndex} `{!invG Σ}.
  #[local] Notation monPred := (monPred I (iPropI Σ)).

  Implicit Type (P : monPred).
  Definition oinv N P : monPred := ⎡ lib.invariants.inv N (∀ i, P i) ⎤%I.

  Lemma inv_obj_oinv N P `{Objective I _ P} : <obj> inv N P ⊣⊢ oinv N P.
  Proof.
    constructor => i.
    rewrite inv_eq /inv_def /oinv monPred_at_embed monPred_at_objectively.
    rewrite lib.invariants.inv_eq /lib.invariants.inv_def.
    iSplit.
    - iIntros "#INV !>" (E NE).
      iSpecialize ("INV" $! i). iDestruct "INV" as "#INV".
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iIntros (i'). by rewrite objective_at.
      + iIntros "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>". by iApply "P".
    - iIntros "#INV" (j) "!>". iIntros (E j1 ? NE).
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iNext. by iApply "P".
      + iIntros (j2 ?) "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>" (j3). by rewrite objective_at.
  Qed.

  Lemma inv_obj_oinv' N P : <obj> inv N (<obj> P) ⊣⊢ oinv N P.
  Proof.
    constructor => i.
    rewrite inv_eq /inv_def /oinv monPred_at_embed monPred_at_objectively.
    rewrite lib.invariants.inv_eq /lib.invariants.inv_def.
    iSplit.
    - iIntros "#INV !>" (E NE).
      iSpecialize ("INV" $! i). iDestruct "INV" as "#INV".
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iIntros (i'). rewrite monPred_at_objectively.
        iNext. by iApply "P".
      + iIntros "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>". rewrite monPred_at_objectively. by iApply "P".
    - iIntros "#INV" (j) "!>". iIntros (E j1 ? NE).
      iMod ("INV" $! E NE) as "[P Close]".
      iIntros "!>". iSplitL "P".
      + iNext. rewrite monPred_at_objectively. by iApply "P".
      + iIntros (j2 ?) "P". iMod ("Close" with "[P]"); last done.
        iIntros "!>" (j3). rewrite monPred_at_objectively.
        by iApply "P".
  Qed.
End oinv.
