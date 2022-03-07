(*
 * Copyright (C) BedRock Systems Inc. 2020-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *
 * This file is derived from code original to the Iris project. That
 * original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/8b5f7383202f19446c3f291050d4d21934a0b0af/theories/bi/lib/atomic.v
 *
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/-/blob/8b5f7383202f19446c3f291050d4d21934a0b0af/LICENSE-CODE
 *)
Require Import stdpp.coPset stdpp.namespaces.
Require Export iris.bi.bi iris.bi.updates.
Require Import bedrock.lang.bi.telescopes.
Require Import iris.proofmode.proofmode.
Set Default Proof Using "Type".

(** * Atomic commits *)
(** Atomic commits are atomic updates without abort. *)

(** atomic commit: an accessor. *)
Definition atomic_commit `{BiFUpd PROP} {TA TB : tele}
    (b : bool) (Eo Ei : coPset)
    (α : TA → PROP) (β Φ : TA → TB → PROP) : PROP :=
  (|={Eo, Ei}=> ∃.. x, α x ∗ ▷?b (∀.. y, β x y ={Ei, Eo}=∗ Φ x y))%I.

#[global] Arguments atomic_commit : simpl never.
#[global] Instance: Params (@atomic_commit) 7 := {}.

(** Notation: Atomic commits *)
Notation "'AC' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 false
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[   ' 'AC'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 false
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[   ' 'AC'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 false
                 Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, β%I) ..))
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
   format "'[   ' 'AC'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO) (TB:=TeleO) false Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[   ' 'AC'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

(** Notation: Atomic commits with a step *)
Notation "'AC1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 true
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[   ' 'AC1'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC1' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 true
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) β%I) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[   ' 'AC1'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC1' '<<' α '>>' @ Eo , Ei '<<' ∃ y1 .. yn , β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO)
                 (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                 true
                 Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, β%I) ..))
                 (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                                (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
   format "'[   ' 'AC1'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∃  y1  ..  yn ,  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Notation "'AC1' '<<' α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_commit (TA:=TeleO) (TB:=TeleO) true Eo Ei
                 (tele_app (TT:=TeleO) α%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
                 (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
   format "'[   ' 'AC1'  '<<'  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Section theory.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types
    (Eo Ei : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .

  #[global] Instance atomic_commit_ne b Eo Ei n :
    Proper (
        pointwise_relation TA (dist n) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        pointwise_relation TA (pointwise_relation TB (dist n)) ==>
        dist n
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof. solve_proper. Qed.

  #[global] Instance atomic_commit_proper b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      pointwise_relation TA (pointwise_relation TB (≡)) ==>
      (≡)
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof. solve_proper. Qed.

  #[global] Instance atomic_commit_mono' b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      (⊢)
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof.
    intros α1 α2 Hα β1 β2 Hβ Φ1 Φ2 HΦ. rewrite/atomic_commit.
    repeat f_equiv; by rewrite ?Hα.
  Qed.

  #[global] Instance atomic_commit_flip_mono' b Eo Ei :
    Proper (
      pointwise_relation TA (≡) ==>
      pointwise_relation TA (pointwise_relation TB (⊢)) ==>
      pointwise_relation TA (pointwise_relation TB (flip (⊢))) ==>
      flip (⊢)
    ) (atomic_commit (PROP:=PROP) b Eo Ei).
  Proof. repeat intro. by rewrite -atomic_commit_mono'. Qed.

  Lemma atomic_commit_atomic1_commit Eo Ei α β Φ :
    atomic_commit false Eo Ei α β Φ -∗ atomic_commit true Eo Ei α β Φ.
  Proof.
    iIntros "AS". iMod "AS" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα".
    iIntros "!>" (y) "Hβ". iApply "Hclose". done.
  Qed.

  Lemma atomic_commit_wand b Eo Ei α β Φ1 Φ2 :
    ▷?b (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    (atomic_commit b Eo Ei α β Φ1 -∗ atomic_commit b Eo Ei α β Φ2).
  Proof.
    iIntros "HP12 AC". iMod "AC" as (x) "[Hα Hclose]".
    iModIntro. iExists x. iFrame "Hα".
    iIntros "!>" (y) "Hβ". iApply "HP12". iApply "Hclose". done.
  Qed.

  Lemma atomic_commit_mask b Eo Ed α β Φ :
    atomic_commit b Eo (Eo∖Ed) α β Φ ⊣⊢
    ∀ E, ⌜Eo ⊆ E⌝ → atomic_commit b E (E∖Ed) α β Φ.
  Proof.
    iSplit; last first.
    { iIntros "Hstep". iApply ("Hstep" with "[% //]"). }
    iIntros "Hstep" (E HE).
    iApply (fupd_mask_frame_acc with "Hstep"); first done.
    iIntros "Hstep". iDestruct "Hstep" as (x) "[Hα Hclose]".
    iIntros "!> Hclose'".
    iExists x. iFrame.
    iIntros "!>" (y) "Hβ". iApply "Hclose'". iApply "Hclose". done.
  Qed.

  Lemma atomic_commit_mask_weaken b Eo1 Eo2 Ei α β Φ :
    Eo1 ⊆ Eo2 →
    atomic_commit b Eo1 Ei α β Φ -∗ atomic_commit b Eo2 Ei α β Φ.
  Proof.
    iIntros (HE) "Hstep".
    iMod fupd_mask_subseteq as "Hclose1"; first done.
    iMod "Hstep" as (x) "[Hα Hclose2]". iIntros "!>". iExists x.
    iFrame. iIntros "!>" (y) "Hβ". iMod ("Hclose2" with "Hβ") as "$". done.
  Qed.

  Lemma atomic_commit_intro b Eo Ei α β Φ :
    Ei ⊆ Eo → ⊢ (∀.. x, α x -∗
    ▷?b (∀.. y, β x y ={Eo}=∗ Φ x y) -∗
    atomic_commit b Eo Ei α β Φ).
  Proof.
    iIntros (? x) "Hα Hclose".
    iMod fupd_mask_subseteq as "Hclose'"; last iModIntro; first set_solver.
    iExists x. iFrame.
    iIntros "!>" (y) "Hβ". iMod "Hclose'" as "_". iApply "Hclose". done.
  Qed.

  Lemma atomic_commit_acc {TA' TB' : tele} b E1 E1' E2 E3 α β Φ
      (α' : TA' → PROP) (β' Φ' : TA' → TB' → PROP) :
    E1' ⊆ E1 →
    atomic_commit b E1' E2 α β Φ -∗
    (∀.. x, α x -∗ atomic_commit b E2 E3 α' β'
            (λ.. x' y', ∃.. y, β x y ∗ (Φ x y ={E1}=∗ Φ' x' y'))) -∗
    atomic_commit b E1 E3 α' β' Φ'.
  Proof.
    iIntros (?) "Hupd Hstep".
    iMod (atomic_commit_mask_weaken with "Hupd") as (x) "[Hα Hclose]";
      first done.
    iMod ("Hstep" with "Hα") as (x') "[Hα' Hclose']".
    iModIntro. iExists x'. iFrame "Hα'". iIntros "!>" (y') "Hβ'".
    iMod ("Hclose'" with "Hβ'") as "Hcont".
    rewrite !tele_app_bind.
    iDestruct "Hcont" as (y) "[Hβ HΦ']".
    iMod ("Hclose" with "Hβ") as "HΦ".
    iApply "HΦ'". done.
  Qed.

  (** Proof mode *)

  (* This lets you eliminate atomic commits with iMod. *)
  #[global] Instance elim_mod_atomic_commit φ b Eo Ei E α β Φ Q Q' :
    (∀ R, ElimModal φ false false (|={E,Ei}=> R) R Q Q') →
    ElimModal (φ ∧ Eo ⊆ E) false false
              (atomic_commit b Eo Ei α β Φ)
              (∃.. x, α x ∗ ▷?b (∀.. y, β x y ={Ei,E}=∗ Φ x y))
              Q Q'.
  Proof.
    intros ?. rewrite /ElimModal /= =>-[??]. iIntros "[AC Hcont]".
    iMod (atomic_commit_mask_weaken with "AC"); first done.
    iApply "Hcont". done.
  Qed.

  (* This lets you open invariants etc. when the goal is an atomic commit. *)
  #[global] Instance elim_acc_atomic_commit {X} b E1 E2 Ei (α' β' : X → PROP)
      γ' α β Φ :
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) α' β' γ'
            (atomic_commit b E1 Ei α β Φ)
            (λ x', atomic_commit b E2 Ei α β
                (λ.. x y, β' x' ∗ (γ' x' -∗? Φ x y))
            )%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x') "[Hα' Hclose]".
    iMod ("Hinner" with "Hα'") as (x) "[Hα Hclose']".
    iMod (fupd_mask_subseteq) as "Hclose''"; last iModIntro; first done.
    iExists x. iFrame.
    iIntros "!>" (y) "Hβ". iMod "Hclose''" as "_".
    iMod ("Hclose'" with "Hβ") as "Hβ'".
    rewrite !tele_app_bind. iDestruct "Hβ'" as "[Hβ' HΦ]".
    iMod ("Hclose" with "Hβ'") as "Hγ'".
    iModIntro. destruct (γ' x'); iApply "HΦ"; done.
  Qed.

  (* Everything that fancy updates can eliminate without changing, atomic
  commits can eliminate as well.  This is a forwarding instance needed becuase
  atomic_commit is becoming opaque. *)
  #[global] Instance elim_modal_atomic_commit p q φ P P' b Eo Ei α β Φ :
    (∀ Q, ElimModal φ p q P P' (|={Eo,Ei}=> Q) (|={Eo,Ei}=> Q)) →
    ElimModal φ p q P P'
              (atomic_commit b Eo Ei α β Φ)
              (atomic_commit b Eo Ei α β Φ).
  Proof. intros Helim. apply Helim. Qed.

End theory.

(* From here on, prevent TC search from implicitly unfolding atomic_commit. *)
#[global] Typeclasses Opaque atomic_commit.

Tactic Notation "iAcIntro" "with" constr(sel) :=
  iStartProof; lazymatch goal with
  | |- environments.envs_entails _ (@atomic_commit ?PROP ?H ?TA ?TB ?b ?Eo ?Ei ?α ?β ?Φ) =>
    iApply (@atomic_commit_intro PROP H TA TB b Eo Ei α β Φ with sel);
    first try solve_ndisj
  | _ => fail "iAcIntro: Goal is not an atomic commit"
  end.

Section derived.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types (α : TA → PROP) (β Φ : TA → TB → PROP).

  (* ppost = (thread-)private postcondition, as opposed to the public or
  _atomic_ postcondition. *)
  Lemma atomic_commit1_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic_commit true Eo Ei α β Φ1 ⊢
    ▷ (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_commit true Eo Ei α β Φ2.
  Proof.
    iIntros "AC1 W". iApply (atomic_commit_wand with "[W] AC1"). done.
  Qed.

  Lemma atomic_commit1_weak_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic_commit true Eo Ei α β Φ1 ⊢
    □ (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_commit true Eo Ei α β Φ2.
  Proof. iIntros "AC1 #W". iApply (atomic_commit1_ppost_wand with "AC1 W"). Qed.

  (* This proof is almost a duplicate of [atomic_commit1_ppost_wand], but due to *)
  (* the different modalities, simplicity we prefer duplicating it rather than *)
  (* doing conditional modality reasoning using [▷?b □?(negb b)] and trying to *)
  (* extend [iAc{1,}Intro] for this scenario. *)
  Lemma atomic_commit_weak_ppost_wand Eo Ei α β Φ1 Φ2 :
    atomic_commit false Eo Ei α β Φ1 ⊢
    □ (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_commit false Eo Ei α β Φ2.
  Proof.
    iIntros "AC1 W". iApply (atomic_commit_wand with "[W] AC1"). done.
  Qed.
End derived.
