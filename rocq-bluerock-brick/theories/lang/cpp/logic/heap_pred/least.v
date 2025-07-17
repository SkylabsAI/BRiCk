(*
 * Copyright (c) 2023 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.lang.cpp.logic.heap_pred.prelude.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  Section leastR.
    Context {A : ofe}.
    Class RepMonoPred (F : (A -> Rep) -> (A -> Rep)) : Prop :=
    { rep_mono_pred : ∀ Φ Ψ : A → Rep,
        NonExpansive Φ → NonExpansive Ψ →
        □ (Forall (p : ptr) (x : A), p |-> Φ x -* p |-> Ψ x) -∗
        Forall (x : A) (p : ptr), p |-> F Φ x -* p |-> F Ψ x
    ; rep_mono_pred_ne : ∀ Φ : A → Rep, NonExpansive Φ → NonExpansive (F Φ) }.

    Definition leastR (F : (A -> Rep) -> (A -> Rep)) : A -> Rep :=
      fun x => Forall Φ : A -n> Rep, (□ Forall (x0 : A), pureR (Forall (p : ptr), p |-> F Φ x0 -* p |-> Φ x0)) -* Φ x.

    #[global] Instance leastR_ne n :
      Proper (pointwise_relation (A -> Rep) (pointwise_relation A (dist n)) ==> dist n ==> dist n) leastR.
    Proof. solve_proper. Qed.
    #[global] Instance leastR_proper :
      Proper (pointwise_relation (A -> Rep) (pointwise_relation A (≡)) ==> (≡) ==> (≡)) leastR.
    Proof. solve_proper. Qed.

    Theorem leastR_fold (F : (A -> Rep) -> (A -> Rep)) {RMP : RepMonoPred F} a :
      F (leastR F) a |-- leastR F a.
    Proof.
      rewrite /leastR/=.
      apply Rep_entails_at=>p.
      rewrite _at_forall.
      iIntros "H" (fx).
      rewrite _at_wand.
      iIntros "#Hi".
      rewrite _at_intuitionistically {2}/pureR.
      rewrite !_at_forall.
      iDestruct "Hi" as "#Hi".
      setoid_rewrite _at_as_Rep.
      iApply "Hi".
      iDestruct (rep_mono_pred _ fx with "[#]") as "X".
      2:{
        iApply ("X" $! _ p).
        unshelve instantiate (1:=OfeMor (λ x : A, Forall Φ : A -n> Rep, □ (Forall x0 : A, pureR (Forall p : ptr, p |-> F Φ x0 -* p |-> Φ x0)) -* Φ x)); last iApply "H".
        solve_proper.
      }
      { iIntros "!>" (??). (* iSpecialize ("Hi" $! x p). *)
        rewrite /=.
        iIntros "X".
        rewrite _at_forall.
        iSpecialize ("X" $! fx).
        rewrite _at_wand.
        iApply "X".
        rewrite _at_intuitionistically.
        iModIntro.
        rewrite _at_forall.
        iIntros (?); rewrite _at_pureR. iIntros (?). iApply "Hi".
      }
    Qed.

    Theorem leastR_unfold (F : (A -> Rep) -> (A -> Rep)) {RMP : RepMonoPred F} a :
      leastR F a |-- F (leastR F) a.
    Proof.
      rewrite /leastR. apply Rep_entails_at=>p.
      iIntros "X".
      unshelve iApply ("X" $! (OfeMor (F (leastR F)))).
      { eapply rep_mono_pred_ne; solve_proper. }
      rewrite _at_intuitionistically.
      iIntros "!>" (??).
      rewrite _at_pureR.
      iApply (rep_mono_pred (F (leastR F)) (leastR F) with "[#]").
      { eapply rep_mono_pred_ne; solve_proper. }
      iIntros "!>" (??). rewrite leastR_fold. eauto.
    Qed.


(*
    Theorem leastR_ind (F : (A -> Rep) -> (A -> Rep)) P `{!NonExpansive P} :
          □ (Forall (p : ptr) (y : A), p |-> F P y -* p |-> P y)
      |-- Forall (p : ptr) x, p |-> leastR F x -* p |-> P x.
    Proof.
      iIntros "#HP" (??) "H".
      rewrite /leastR _at_forall.
      unshelve iSpecialize ("H" $! (OfeMor P)); simpl.
      { refine _. }
      rewrite !_at_wand !_at_intuitionistically !_at_forall.
      iApply "H".
      iIntros "!>" (?). rewrite _at_pureR.
      iIntros (?); iApply "HP".
    Qed.
*)

    Theorem leastR_ind (F : (A -> Rep) -> (A -> Rep)) (P : ptr -> A -> mpred) {_ : forall p, NonExpansive (P p)} (p : ptr) x :
          □ (Forall (p : ptr) (y : A), p |-> F (fun x => as_Rep (fun p => P p x)) y -* P p y)
      |-- p |-> leastR F x -* P p x.
    Proof.
      iIntros "#HP H".
      rewrite /leastR _at_forall.
      unshelve iSpecialize ("H" $! (OfeMor (fun x => as_Rep (fun p => P p x)))); simpl.
      { intro.
        red; intros. red; intros. simpl.
        apply as_Rep_ne=>?. apply H. apply H0. }
      rewrite !_at_wand !_at_intuitionistically !_at_forall.
      rewrite _at_as_Rep.
      iApply "H".
      iIntros "!>" (?). rewrite _at_pureR.
      iIntros (?). rewrite _at_as_Rep; iApply "HP".
    Qed.

    Lemma leastR_indR (F : (A -> Rep) -> (A -> Rep)) (P : A -> Rep) {_ : NonExpansive P}
      (_ : Proper (pointwise_relation _ (⊢) ==> pointwise_relation _ (⊢)) F) x :
          □ (pureR $ Forall (p : ptr) (y : A), p |-> F P y -* p |-> P y)
      |-- leastR F x -* P x.
    Proof.
      apply Rep_entails_at=>p.
      rewrite _at_intuitionistically _at_pureR.
      iIntros "#HP".
      rewrite _at_wand.
      unshelve iApply (leastR_ind _ (fun p x => _at p (P x))).
      { simpl. intros ???? HH.
        apply _at_ne. apply H. assumption. }
      iIntros "!>" (??).
      iIntros "X".
      iApply "HP".
      iClear "HP".
      iStopProof.
      f_equiv. apply H0.
      intro.
      rewrite __at.unlock/AT_at /=.
      rewrite as_Rep.unlock @at_aux.unlock.
      generalize dependent RepI.unlock.
      unfold Rep in *.
      generalize dependent @RepI; intros; subst; simpl.
      done.
    Qed.

    #[global] Instance leastR_timeless F :
      (forall fx, Timeless1 fx -> Timeless1 (F fx)) ->
      Timeless1 (leastR F).
    Proof.
      intros. red. iIntros "X".
    Abort. (* unprovable *)

  End leastR.

End with_cpp.
