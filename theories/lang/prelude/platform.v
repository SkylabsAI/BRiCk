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

(** ** bitsizes *)
Variant bitsize : Set :=
  | W8 | W16 | W32 | W64 | W128.

Definition bytesN (b : bitsize) : N :=
  match b with
  | W8 => 1
  | W16 => 2
  | W32 => 4
  | W64 => 8
  | W128 => 16
  end.

Definition bitsN (b : bitsize) : N :=
  match b with
  | W8 => 8
  | W16 => 16
  | W32 => 32
  | W64 => 64
  | W128 => 128
  end.

Lemma bytes_bits b : (8 * bytesN b = bitsN b)%N.
Proof. by destruct b. Qed.

#[global] Instance bitsize_eq_dec: EqDecision bitsize.
Proof. solve_decision. Defined.
#[global] Instance bitsize_countable : Countable bitsize.
Proof.
  apply (inj_countable'
            (λ s,
              match s with
              | W8 => 1
              | W16 => 2
              | W32 => 3
              | W64 => 4
              | W128 => 5
              end)
            (λ b,
              match b with
              | 1 => W8
              | 2 => W16
              | 3 => W32
              | 4 => W64
              | 5 => W128
              | _ => W8
              end)).
  abstract (by intros []).
Defined.
