(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.numbers.

(** * Splitting and combining booleans on [&&] *)
(**
Overview:

- [SplitAndB], [CombineAndB] split and combine boolean expressions
built up from constants and [&&]. They simplify their outputs.
*)

(**
Our rules are syntactic: All definitions appearing in input positions
should be opaque for typeclass resolution.
*)
#[global] Hint Opaque andb : typeclass_instances.

#[local] Notation Cut := TCNoBackTrack.

(**
[SplitAndB b b1 b2] splits boolean [b] into [b1], [b2] s.t. [b = b1 &&
b2], adjusting the outputs [b1], [b2] for readability.
*)
Class SplitAndB (b b1 b2 : bool) : Prop := split_andb : b = b1 && b2.
#[global] Hint Mode SplitAndB + - - : typeclass_instances.
#[global] Arguments SplitAndB : simpl never.
#[global] Arguments split_andb _ {_ _ _} : assert.

#[global] Instance split_andb_andb b1 b2 : SplitAndB (b1 && b2) b1 b2 | 10.
Proof. done. Qed.

#[global] Instance split_andb_diag b : SplitAndB b b b | 50.
Proof. rewrite /SplitAndB. by rewrite andb_diag. Qed.

(**
[CombineAndB b1 b2 b] combines booleans [b1], [b2] into [b = b1 &&
b2], adjusting the output [b] for readability.
*)
Class CombineAndB (b1 b2 b : bool) : Prop := combine_andb : b1 && b2 = b.
#[global] Hint Mode CombineAndB + + - : typeclass_instances.
#[global] Arguments CombineAndB : simpl never.
#[global] Arguments combine_andb _ _ {_ _} : assert.

Module combine_andb.

  (**
  We use this auxiliary judgment to [Cut] in [CombineAndB].
  *)
  Class Combine (b1 b2 b : bool) : Prop := combine : b1 && b2 = b.
  #[global] Hint Mode Combine + + - : typeclass_instances.
  #[global] Arguments Combine : simpl never.
  #[global] Arguments combine _ _ {_ _} : assert.
  Notation COMBINE q1 q2 q := (Cut (Combine q1 q2 q)) (only parsing).

  (** [false] absorbing *)
  #[global] Instance combine_0x b : Combine false b false | 10.
  Proof. done. Qed.
  #[global] Instance combine_x0 b : Combine b false false | 15.
  Proof. rewrite /Combine. by rewrite right_absorb_L. Qed.

  (** [true] an identity *)
  #[global] Instance combine_1x b : Combine true b b | 10.
  Proof. done. Qed.
  #[global] Instance combine_x1 b : Combine b true b | 15.
  Proof. rewrite /Combine. by rewrite right_id_L. Qed.

  (** [b && b --> b] *)
  #[global] Instance combine_diag b : Combine b b b| 50.
  Proof. rewrite /Combine. by rewrite andb_diag. Qed.

  #[global] Instance combine_xx b1 b2 : Combine b1 b2 (b1 && b2) | 51.
  Proof. done. Qed.

End combine_andb.

#[global] Instance combine_andb_combine b b1 b2 :
  combine_andb.COMBINE b b1 b2 -> CombineAndB b b1 b2 | 10.
Proof. by case. Qed.
