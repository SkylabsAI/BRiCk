(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base bedrock.prelude.numbers.

#[local] Open Scope Z_scope.

(** ** Endianness -- TODO move *)
Variant endian : Set := Little | Big.
#[global] Instance endian_dec : EqDecision endian.
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

End bitsize.

(** ** Signed and Unsigned *)
Variant signed : Set := Signed | Unsigned.
#[global] Instance signed_eq_dec: EqDecision signed.
Proof. solve_decision. Defined.
#[global] Instance signed_countable : Countable signed.
Proof.
  apply (inj_countable'
    (λ s, if s is Signed then true else false)
    (λ b, if b then Signed else Unsigned)).
  abstract (by intros []).
Defined.

(** ** Integral Types *)

(** [int_type] provides the standard C++ primitive integral types *)
Variant int_type : Set :=
| Schar
| Sshort
| Sint
| Slong
| Slonglong
| S128.
#[global] Instance bitsize_eq: EqDecision int_type.
Proof. solve_decision. Defined.
#[global] Instance bitsize_countable : Countable int_type.
Proof.
  apply (inj_countable'
    (λ b,
      match b with
      | Schar => 0 | Sshort => 1 | Sint => 2 | Slong => 3 | Slonglong => 4 | S128 => 5
      end)
    (λ n,
      match n with
      | 0 => Schar | 1 => Sshort | 2 => Sint | 3 => Slong | 4 => Slonglong | 5 => S128
      | _ => Schar	(* dummy *)
      end)).
  abstract (by intros []).
Defined.

Definition bytesNat (s : int_type) : nat :=
  match s with
  | Schar     => 1
  | Sshort    => 2
  | Sint      => 4
  | Slong     => 8
  | Slonglong => 8
  | S128      => 16
  end.

Definition bytesN (s : int_type) : N :=
  N.of_nat (bytesNat s).

(* TODO: make a Notation? *)
Definition bytesZ (s : int_type) : Z :=
  Z.of_N (bytesN s).


Definition bitsN (s : int_type) : N :=
  8 * bytesN s.

(* A notation because is is not a new abstraction *)
Definition bitsZ s := (Z.of_N (bitsN s)).


Bind Scope N_scope with int_type.

Lemma of_size_gt_O w :
  (0 < 2 ^ bitsZ w)%Z.
Proof. destruct w; reflexivity. Qed.
(* Hint Resolve of_size_gt_O. *)

Definition max_val (bits : int_type) (sgn : signed) : Z :=
  match sgn with
  | Signed => pow2N (bitsN bits - 1) - 1
  | Unsigned => pow2N (bitsN bits) - 1
  end%N.

Definition min_val (bits : int_type) (sgn : signed) : Z :=
  match sgn with
  | Unsigned => 0
  | Signed => - pow2N (bitsN bits - 1)
  end.

Definition bound (bits : int_type) (sgn : signed) (v : Z) : Prop :=
  min_val bits sgn <= v <= max_val bits sgn.


(*
(** This record is what would be needed to support different compiler settings,
    e.g. the precision of [long] being 32 vs 64.
 *)
Section with_arith.
  Class ArithSettings : Set :=
    { char_bits : N
    ; short_bits : N
    ; int_bits : N
    ; long_bits : N
    ; longlong_bits : N
    ; char_bound : (8 <= char_bits)%N
    ; short_bound : (16 <= short_bits)%N
    ; int_bound : (32 <= int_bits)%N
    ; long_bound : (32 <= long_bits)%N
    ; longlong_bound : (64 <= longlong_bits)%N
    ; char_short : (char_bits <= short_bits)%N
    ; short_int : (short_bits <= int_bits)%N
    ; int_long : (int_bits <= long_bits)%N
    ; long_longlong : (long_bits <= longlong_bits)%N
    }.


  Context {AS : ArithSettings}.
  Definition bitsN (sz : int_type) : N :=
    match sz with
    | Schar => char_bits
    | Sshort => short_bits
    | Sint => int_bits
    | Slong => long_bits
    | Slonglong => longlong_bits
    end.

End with_arith.
*)
