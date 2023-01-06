(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.numbers.

(** ** Endianness -- TODO move *)
Variant endian : Set := Little | Big.
#[global] Instance endian_eq_dec : EqDecision endian.
Proof. solve_decision. Defined.

(** ** bitsizes -- TODO represent simply as positive? *)
Module bitsize.
  Variant t : Set :=
    | W8 | W16 | W32 | W64 | W80 | W128.

  Definition bitsN (b : t) : N :=
    match b with
    | W8 => 8
    | W16 => 16
    | W32 => 32
    | W64 => 64
    | W80 => 80
    | W128 => 128
    end.

  Notation bitsZ b := (Z.of_N (bitsN b)).

  #[global] Instance t_eq_dec: EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
             (λ s,
               match s with
               | W8 => 1
               | W16 => 2
               | W32 => 3
               | W64 => 4
               | W80 => 5
               | W128 => 6
               end)
             (λ b,
               match b with
               | 1 => W8
               | 2 => W16
               | 3 => W32
               | 4 => W64
               | 5 => W80
               | 6 => W128
               | _ => W8
               end)).
    abstract (by intros []).
  Defined.

  Definition bytesN (b : t) : N :=
    match b with
    | W8 => 1
    | W16 => 2
    | W32 => 4
    | W64 => 8
    | W80 => 10
    | W128 => 16
    end.

  Lemma bytes_bits b : (8 * bytesN b = bitsN b)%N.
  Proof. by destruct b. Qed.
End bitsize.
Notation bitsize := bitsize.t.
