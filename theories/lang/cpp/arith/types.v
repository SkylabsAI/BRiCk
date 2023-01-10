(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base bedrock.prelude.numbers.

#[local] Open Scope Z_scope.

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
| Ichar
| Ishort
| Iint
| Ilong
| Ilong_long
| I128.
#[global] Instance bitsize_eq: EqDecision int_type.
Proof. solve_decision. Defined.
#[global] Instance bitsize_countable : Countable int_type.
Proof.
  apply (inj_countable'
    (λ b,
      match b with
      | Ichar => 0 | Ishort => 1 | Iint => 2 | Ilong => 3 | Ilong_long => 4 | I128 => 5
      end)
    (λ n,
      match n with
      | 0 => Ichar | 1 => Ishort | 2 => Iint | 3 => Ilong | 4 => Ilong_long | 5 => I128
      | _ => Ichar	(* dummy *)
      end)).
  abstract (by intros []).
Defined.

Definition bytesNat (s : int_type) : nat :=
  match s with
  | Ichar     => 1
  | Ishort    => 2
  | Iint      => 4
  | Ilong     => 8
  | Ilong_long => 8
  | I128      => 16
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
  | Signed => 2 ^ (bitsN bits - 1) - 1
  | Unsigned => 2 ^ (bitsN bits) - 1
  end%N.

Definition min_val (bits : int_type) (sgn : signed) : Z :=
  match sgn with
  | Unsigned => 0
  | Signed => - (2 ^ (bitsN bits - 1))
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
