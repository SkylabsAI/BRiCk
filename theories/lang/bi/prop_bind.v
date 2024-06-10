(*
 * Copyright (C) BedRock Systems Inc. 2024
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 *)

(* Simple monadic bind for binary BI predicates *)
Require Import stdpp.coPset stdpp.namespaces.
Require Import bedrock.lang.bi.telescopes.
Require Import bedrock.lang.proofmode.proofmode.
Require Import bedrock.lang.bi.atomic_commit.


Definition M2 {PROP : bi} (TA TB : Type) : Type :=
  (TA -> TB -> PROP) -> PROP.

Definition mbind2 {PROP : bi} {TA1 TB1 TA2 TB2}
  (FAB : TA1 -> TB1 -> M2 TA2 TB2) (fa : M2 TA1 TB1) : M2 TA2 TB2 :=
  λ Pb : TA2 -> TB2 -> PROP, fa (λ a b, FAB a b Pb).

Definition mret2 {PROP : bi} {TA TB : Type} (a : TA) (b : TB) : M2 TA TB :=
  λ f : TA -> TB -> PROP, f a b.

Definition mpar2 {PROP : bi} {TA1 TB1 TA2 TB2}
    (ac1 : M2 TA1 TB1) (ac2 : M2 TA2 TB2) : M2 (TA1 * TA2) (TB1 * TB2) :=
  (λ Q : TA1 * TA2 -> TB1 * TB2 -> PROP,
    ∃ Q1 Q2, ac1 Q1 ∗ ac2 Q2 ∗ (∀ x1 x2 y1 y2, Q1 x1 y1 -∗ Q2 x2 y2 -∗ Q (x1,x2) (y1,y2)))%I.

(* Parallel bind is commutative *)
Lemma mpar2_commutative {PROP : bi} {TA1 TB1 TA2 TB2}
    (ac1 : M2 TA1 TB1) (ac2 : M2 TA2 TB2) (Q : _ -> _ -> PROP) :
  mpar2 ac1 ac2 Q ⊣⊢ mpar2 ac2 ac1 (λ '(x2, x1) '(y2,y1), Q (x1,x2) (y1,y2)).
Proof.
  rewrite /mpar2. iSplit.
  - iDestruct 1 as (Q1 Q2) "(A1 & A2 & C)".
    iExists Q2, Q1. iFrame. iIntros (x2 x1 y2 y1) "Q2 Q1".
    iApply ("C" with "Q1 Q2").
  - iDestruct 1 as (Q2 Q1) "(A2 & A1 & C)".
    iExists Q1, Q2. iFrame. iIntros (x1 x2 y1 y2) "Q1 Q2".
    iApply ("C" with "Q2 Q1").
Qed.

(* Sequential bind is letI* *)
Lemma mbind2_letI {PROP : bi} {TA1 TB1 TA2 TB2}
    f (ac : M2 TA1 TB1) (Q : TA2 -> TB2 -> PROP) :
  mbind2 f ac Q ⊣⊢ letI* x, y := ac in f x y Q.
Proof. done. Qed.

(** Notation: private post as mbind2 *)
Notation "'mAC1' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' ∀∀ y1 .. yn , β '>>' ';' Φ" :=
  (mbind2
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                        λ x1, .. (λ xn,
                          tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                          (λ y1, .. (λ yn, Φ%I) .. )
                          ) .. )
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
                          ) .. ))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[   ' 'mAC1'  '<<'  ∃∃  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∀∀  y1  ..  yn ,  β  '>>'  ';'  Φ ']' ']'") : bi_scope.


(** Notation: without private post *)
Notation "'mAC1' '<<' ∃∃ x1 .. xn , α '>>' @ Eo , Ei '<<' ∀∀ y1 .. yn , β '>>'" :=
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
                        ) .. ))
  (at level 20, Eo, Ei, α, β at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[   ' 'mAC1'  '<<'  ∃∃  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  ∀∀  y1  ..  yn ,  β  '>>' ']' ']'") : bi_scope.


(** Notation: mpar2 followed by mbind2 *)
Notation "'mAC1' '<<' ∃∃ x1 .. xn , α1 '>>' @ Eo1 , Ei1 '<<' ∀∀ y1 .. yn , β1 '>>' '||' 'mAC1' '<<' ∃∃ u1 .. un , α2 '>>' @ Eo2 , Ei2 '<<' ∀∀ v1 .. vn , β2 '>>' ';' Φ" :=
  (mbind2
    (λ '(x,u) '(y,v),
      tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
        (λ x1, .. (λ xn,
          tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
            (λ y1, .. (λ yn,
              tele_app (TT:=TeleS (λ u1, .. (TeleS (λ un, TeleO)) .. ))
                (λ u1, .. (λ un,
                  tele_app (TT:=TeleS (λ v1, .. (TeleS (λ vn, TeleO)) .. ))
                    (λ v1, .. (λ vn, Φ%I) .. ) v
                ) ..) u
            ) ..) y
        ) ..) x)
    (mpar2
      (atomic_commit (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                    (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                    true
                    Eo1 Ei1
                    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                          λ x1, .. (λ xn, α1%I) ..)
                    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                          λ x1, .. (λ xn,
                            tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                            (λ y1, .. (λ yn, β1%I) .. )
                            ) .. ))
      (atomic_commit (TA:=TeleS (λ u1, .. (TeleS (λ un, TeleO)) .. ))
                    (TB:=TeleS (λ v1, .. (TeleS (λ vn, TeleO)) .. ))
                    true
                    Eo2 Ei2
                    (tele_app (TT:=TeleS (λ u1, .. (TeleS (λ un, TeleO)) .. )) $
                          λ u1, .. (λ un, α2%I) ..)
                    (tele_app (TT:=TeleS (λ u1, .. (TeleS (λ un, TeleO)) .. )) $
                          λ u1, .. (λ un,
                            tele_app (TT:=TeleS (λ v1, .. (TeleS (λ vn, TeleO)) .. ))
                            (λ v1, .. (λ vn, β2%I) .. )
                            ) .. )))
  )
  (at level 20, Eo1, Ei1, α1, β1, α2, β2, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder, u1 binder, un binder, v1 binder, vn binder) : bi_scope.


Section tests_type.
  Context {PROP : bi}.
  Context `{!BiFUpd PROP}.
  Context {TA1 TB1 TA2 TB2 TA3 TB3 : tele}.
  Context (Eo1 Ei1 Eo2 Ei2 Eo3 Ei3 : coPset).
  Context (α1 : TA1 -> PROP) (β1 : TA1 -> TB1 -> PROP).
  Context (α2 : TA2 -> PROP) (β2 : TA2 -> TB2 -> PROP).
  Context (α3 : TA3 -> PROP) (β3 Φ3 : TA3 -> TB3 -> PROP).

  Let ac1 := atomic_commit true Eo1 Ei1 α1 β1.
  Let ac2 := atomic_commit true Eo2 Ei2 α2 β2.
  Let ac3 := atomic_commit false Eo3 Ei3 α3 β3.

  (* ac1 followed by ac2 *)
  Let ac1s2 := mbind2 (λ _ _, ac2) ac1.

  (* ac1 followed by ac2 and then ac3 *)
  Let ac1s2s3 := mbind2 (λ _ _, ac3) ac1s2.

  (* ac1 unordered with ac2 followed by ac3 *)
  Let ac1p2s3 := mbind2 (λ _ _, ac3) (mpar2 ac1 ac2).

  (* with post-condition Φ3 *)
  Let ac1p2s3closed := ac1p2s3 Φ3.

End tests_type.

Section tests_notation.
  Context {PROP : bi}.
  Context `{!BiFUpd PROP}.

  Let ac1 : _ -> PROP :=
    (mAC1 << ∃∃ x : N, [| x = 5%N |] >> @ top, empty
          << ∀∀ y : N, [| y = x + 5 |]%N >> ;
    (λ (_ : TeleO -> TeleO -> _), emp))%I.

  #[local] Definition ac2 : PROP :=
    (mAC1 << ∃∃ x : N, [| x = 5%N |] >> @ top, empty
                << ∀∀ y : N, [| y = x + 5 |]%N >> ;
    (mAC1 << ∃∃ u : Z, [| u = x |] >> @ top, empty
          << ∀∀ v : Z, [| v = u + y + 5 |]%Z >> ;
          (λ (Q : TeleO -> TeleO -> _), [| v = u + y + 5 |]%Z ∗ Q () () )))%I (λ _ _, [| 5 = 5 |])%I.

  #[local] Lemma blah_ac2 : ⊢ ac2.
  Proof.
    rewrite /ac2.
    iAcIntro. rewrite /commit_acc.
    iMod (fupd_mask_subseteq empty) as "Close"; [done|].
    iIntros "!>". iExists 5%N.
    iSplitR. { by iIntros "!%". }
    iIntros "!>" (y Eqy). iMod "Close" as "_".
    iIntros "!>".
    rewrite /mbind2 /=.
    iAcIntro. rewrite /commit_acc.
    iMod (fupd_mask_subseteq empty) as "Close"; [done|].
    iIntros "!>". iExists 5%Z.
    iSplitR. { by iIntros "!%". }
    iIntros (v) "!>". iIntros (Eqv).
    iMod "Close". by iFrame (Eqv).
  Qed.

  (* (AC1; AC1 ; AC1) Q *)
  #[local] Definition ac2' : PROP :=
    (
      mAC1 << ∃∃ x : N, [| x = 5%N |] >> @ ⊤, ∅ << ∀∀ y : N, [| y = x + 5 |]%N >> ;
      mAC1 << ∃∃ u : Z, [| u = x |] >> @ ⊤, ∅ << ∀∀ v : Z, [| v = u + y + 5 |]%Z >> ;
      mAC1 << ∃∃ s : Z, [| s = x + u |]%Z >> @ ⊤, ∅ << ∀∀ t : Z, [| t = x + y + u + v + s |]%Z >>
    ) (λ _ _, [| 5 = 5 |]).


  (* ((AC1 || AC1) ; AC1) Q *)
  #[local] Definition ac3 : PROP :=
    ( 
          mAC1 << ∃∃ x : N, [| x = 5%N |] >> @ ⊤, ∅ << ∀∀ y : N, [| y = x + 5 |]%N >>
      ||  mAC1 << ∃∃ u : Z, [| u = 10 |] >> @ ⊤, ∅ << ∀∀ v : Z, [| v = u + 5 |]%Z >> ;
      mAC1  << ∃∃ s : Z, [| s = u + x |]%Z >> @ ⊤, ∅ << ∀∀ t : Z, [| t = v + y + 5 |]%Z >>
    ) (λ _ _, emp).

  #[local] Lemma blah_ac3 : ⊢ ac3.
  Proof.
    rewrite /ac3.
    (* rewrite mpar2_commutative. <- need Proper instances *)
    iExists (tele_app (TT:=[tele _]) (λ x, tele_app (TT:=[tele _]) (λ y, [| x = 5 ∧ y = 10 |]%N))).
    iExists (tele_app (TT:=[tele _]) (λ u, tele_app (TT:=[tele _]) (λ v, [| u = 10 ∧ v = 15 |]%Z))).
    iSplitL; last iSplitL.
    - iAcIntro. rewrite /commit_acc.
      iMod (fupd_mask_subseteq empty) as "Close"; [done|].
      iIntros "!>". iExists 5%N.
      iSplitR. { by iIntros "!%". }
      iIntros "!>" (y Eqy). iMod "Close" as "_".
      subst y. done.
    - iAcIntro. rewrite /commit_acc.
      iMod (fupd_mask_subseteq empty) as "Close"; [done|].
      iIntros "!>". iExists 10%Z.
      iSplitR. { by iIntros "!%". }
      iIntros "!>" (v Eqv). iMod "Close" as "_".
      subst v. done.
    - iIntros ([x []] [u []] [y []] [v []]). simpl.
      iIntros ([??] [??]); subst.
      iAcIntro. rewrite /commit_acc.
      iMod (fupd_mask_subseteq empty) as "Close"; [done|].
      iIntros "!>".
      iExists 15%Z. iSplitR; first done.
      iIntros (t) "!>". iIntros (Eqt). by iFrame "Close".
  Qed.
End tests_notation.
