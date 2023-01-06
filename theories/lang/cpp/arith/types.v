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

(** ** Integer types
    See <https://en.cppreference.com/w/cpp/language/types>
 *)
Module int_type.
  (* the rank <https://eel.is/c++draft/conv.rank> *)
  Variant t : Set :=
    | Schar
    | Sshort
    | Sint
    | Slong
    | Slonglong
    | S128.
  Notation rank := t (only parsing).

  Notation Ichar := Schar (only parsing).
  Notation Ishort := Sshort (only parsing).
  Notation Iint := Sint (only parsing).
  Notation Ilong := Slong (only parsing).
  (** warning: LLP64 model uses [long_bits := W32] *)
  Notation Ilonglong := Slonglong (only parsing).

  (* NOTE: These are hardcoded to LP64 model *)
  Definition bytesN (t : t) : N :=
    match t with
    | Schar     => 1
    | Sshort    => 2
    | Sint      => 4
    | Slong     => 8
    | Slonglong => 8
    | S128      => 16
    end.

  Definition bitsN (t : t) : N :=
    8 * bytesN t.

  Definition t_le (a b : t) : Prop :=
    (bytesN a <= bytesN b)%N.

  #[global] Instance t_le_dec : RelDecision t_le :=
    fun a b => N.le_dec (bytesN a) (bytesN b).

  (* [max] on the rank. *)
  Definition t_max (a b : t) : t :=
    if bool_decide (t_le a b) then b else a.

  (* TODO: deprecate
  Lemma of_size_gt_O w :
    (0 < 2 ^ bitsN w)%Z.
  Proof. destruct w; reflexivity. Qed.
  Hint Resolve of_size_gt_O. *)

End int_type.
Notation int_type := int_type.t.


Definition max_val (bits : int_type) (sgn : signed) : Z :=
  match sgn with
  | Signed => pow2N (int_type.bitsN bits - 1) - 1
  | Unsigned => pow2N (int_type.bitsN bits) - 1
  end%N.

Definition min_val (bits : int_type) (sgn : signed) : Z :=
  match sgn with
  | Unsigned => 0
  | Signed => - pow2N (int_type.bitsN bits - 1)
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
