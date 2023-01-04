(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From bedrock.lang.cpp.algebra Require Import cv.
From bedrock.lang.bi Require Import prelude split_andb split_frac.
Require Import iris.proofmode.proofmode.
Import ChargeNotation.

#[local] Set Printing Coercions.

(** * Splitting and combining const/mutable fractional things *)
(**
Overview:

- [SplitcQp], [CombinecQp] split and combine terms of type [cQp.t] built
up from booleans, fractions, and [op]
*)

(**
Our rules are syntactic: All operations appearing in input positions
should be opaque for typeclass resolution.
*)
#[global] Hint Opaque op : typeclass_instances.

#[local] Notation Cut := TCNoBackTrack.

(**
[SplitcQp cv cv1 cv2] splits [cv : cQp.t] into [cv1], [cv2] s.t. [cv =
cv1 ⋅ cv2], adjusting the outputs [cv1], [cv2] for readabilty.
*)
Class SplitcQp (cv cv1 cv2 : cQp.t) : Prop := split_cv : cv = cv1 ⋅ cv2.
#[global] Hint Mode SplitcQp + - - : typeclass_instances.
#[global] Arguments SplitcQp : simpl never.
#[global] Arguments split_cv _ {_ _ _} : assert.

Module split_cv.

  (**
  We use this auxiliary judgment to [Cut] in [SplitcQp].
  *)
  Class Split (cv cv1 cv2 : cQp.t) : Prop := split : cv = cv1 ⋅ cv2.
  #[global] Hint Mode Split + - - : typeclass_instances.
  #[global] Arguments Split : simpl never.
  #[global] Arguments split _ {_ _ _} : assert.
  Notation SPLIT cv1 cv2 cv := (Cut (Split cv1 cv2 cv)) (only parsing).

  #[global] Instance split_op cv1 cv2 : Split (cv1 ⋅ cv2) cv1 cv2 | 10.
  Proof. done. Qed.

  #[global] Instance split_mk c c1 c2 q q1 q2 :
    SplitAndB c c1 c2 ->
    SplitFrac q q1 q2 ->
    Split (cQp.mk c q) (cQp.mk c1 q1) (cQp.mk c2 q2) | 10.
  Proof.
    intros. rewrite /Split cQp.t_op/=. by f_equal.
  Qed.

  #[global] Instance split_var cv c1 c2 cv1 cv2 :
    SplitAndB (cQp.is_const cv) c1 c2 ->
    SplitFrac (cQp.frac cv) cv1 cv2 ->
    Split cv (cQp.mk c1 cv1) (cQp.mk c2 cv2) | 50.
  Proof.
    intros. rewrite /Split cQp.t_op/=. rewrite (cQp.eta cv). by f_equal.
  Qed.

End split_cv.

#[global] Instance split_cv_split cv cv1 cv2 :
  split_cv.SPLIT cv cv1 cv2 -> SplitcQp cv cv1 cv2 | 10.
Proof. by case. Qed.

(**
[CombinecQp cv1 cv2 cv] combine [cv1, cv2 : cQp.t] into [cv = cv1 ⋅ cv2],
adjusting the output [cv] for readability.
*)
Class CombinecQp (cv1 cv2 cv : cQp.t) : Prop := combine_cv : cv1 ⋅ cv2 = cv.
#[global] Hint Mode CombinecQp + + - : typeclass_instances.
#[global] Arguments CombinecQp : simpl never.
#[global] Arguments combine_cv _ _ {_ _} : assert.

Module combine_cv.

  (**
  Step 1: Combine the component parts, producing a possibly ugly term.
  *)
  Class Combine (cv1 cv2 cv : cQp.t) : Prop := combine : cv1 ⋅ cv2 = cv.
  #[global] Hint Mode Combine + + - : typeclass_instances.
  #[global] Arguments Combine : simpl never.
  #[global] Arguments combine _ _ {_ _} : assert.

  #[global] Instance combine_mk_mk c1 c2 c q1 q2 q :
    CombineAndB c1 c2 c -> CombineFrac q1 q2 q ->
    Combine (cQp.mk c1 q1) (cQp.mk c2 q2) (cQp.mk c q) | 10.
  Proof.
    intros. rewrite /Combine cQp.t_op /=.
    by rewrite combine_andb combine_frac.
  Qed.

  #[global] Instance combine_mk_any c1 c cv1 cv2 :
    CombineAndB c1 (cQp.is_const cv2) c ->
    Combine (cQp.mk c1 cv1) cv2 (cQp.mk c (cv1 + cQp.frac cv2)) | 15.
  Proof.
    intros. rewrite /Combine cQp.t_op /=. by rewrite combine_andb.
  Qed.
  #[global] Instance combine_any_mk c2 c cv2 cv1 :
    CombineAndB (cQp.is_const cv1) c2 c ->
    Combine cv1 (cQp.mk c2 cv2) (cQp.mk c (cQp.frac cv1 + cv2)) | 15.
  Proof.
    intros. rewrite /Combine cQp.t_op /=. by rewrite combine_andb.
  Qed.

  #[global] Instance combine_any_any cv1 cv2 : Combine cv1 cv2 (cv1 ⋅ cv2) | 50.
  Proof. done. Qed.

  (**
  Step 2: Make the term from step (1) prettier.
  *)

  Class Prettify (cv' cv : cQp.t) : Prop := prettify : cv' = cv.
  #[global] Hint Mode Prettify + - : typeclass_instances.
  #[global] Arguments Prettify : simpl never.
  #[global] Arguments prettify _ {_ _} : assert.

  #[global] Instance prettify_eta c : Prettify (cQp.mk (cQp.is_const c) (cQp.frac c)) c | 10.
  Proof. done. Qed.
  #[global] Instance prettify_skip c : Prettify c c | 50.
  Proof. done. Qed.

End combine_cv.

#[global] Instance combine_cv_instance c1 c2 chat c :
  combine_cv.Combine c1 c2 chat -> combine_cv.Prettify chat c ->
  CombinecQp c1 c2 c | 10.
Proof.
  by rewrite /combine_cv.Combine /combine_cv.Prettify=><-.
Qed.
