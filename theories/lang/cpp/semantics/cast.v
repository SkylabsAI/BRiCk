(*
 * Copyright (c) 2020-22 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** ** Primitive Conversions

    This file covers conversions between primitive types.
 *)
From bedrock.prelude Require Import base numbers.
From bedrock.lang.cpp.arith Require Export operator.
From bedrock.lang.cpp Require Import ast semantics.values semantics.promotion.

#[local] Open Scope Z_scope.

(** Architecture independent character values

    To unify the *value* representation of characters, we store characters
    in an architecture-independent way as [unsigned] integers (using [N]).

    Effectively, this is like storing values of type `char` as if they were
    `unsigned char` and re-interpreting the bits as `signed char` before
    performing operations on them. Note that because this is a logical-only
    conversion, it does not require a boundedness check, i.e. for 8-bit
    characters, 255 should mean -1 on a signed platform *regardless* of the
    C++ language version.

    The conversion from this representation to its integral representation
    is typed *on both sides* meaning that you need both the source and the
    target type information in order to perfom the conversion.

    The low-level conversion functions are included here to fully document
    the representation. [conv_int] abstracts these details for use in the
    rest of the semantics.
 *)
Definition to_char (from_sz : N) (from_sgn : signed) (to_bits : N) (*to_sgn : signed*) (v : Z) : N :=
  if from_sgn is Signed then
    if bool_decide (v < 0) then
      Z.to_N $ 2^to_bits - (v `mod` 2^to_bits)
    else Z.to_N $ to_unsigned_bits from_sz v
  else Z.to_N $ to_unsigned_bits from_sz v.

Definition of_char (from_bits : N) (from_sgn : signed) (to_bits : N) (to_sgn : signed) (n : N) : Z :=
  (* first we need to sign extend using frm_sgn *)
  let n : Z :=
    if from_sgn is Signed then
      if bool_decide (n < 2^(from_bits-1)) then n else -n + 1
    else n in
  if to_sgn is Signed then to_signed_bits to_bits n else to_unsigned_bits to_bits n.

(* suppose that you are in an architecture with unsigned characters
    and you wrote (128)
  *)

Succeed Example TEST : of_char 8 Signed 32 Signed 1 = 1 := eq_refl.
Succeed Example TEST : of_char 8 Signed 32 Signed 128 = -127 := eq_refl.
Succeed Example TEST : of_char 8 Signed 32 Signed 127 = 127 := eq_refl.
Succeed Example TEST : of_char 8 Signed 16 Unsigned 128 = 65409 := eq_refl.
(* END TODO move to syntax *)

(** Integral conversions. For use in the semantics of C++ operators.

    TODO documentation needed.
  *)
Definition conv_int {σ : genv} (tu : translation_unit) (from to : type) (v v' : val) : Prop :=
  match underlying_type tu from , underlying_type tu to with
  | Tbool , Tnum _ _ =>
      match is_true v with
      | Some v => v' = Vbool v
      | _ => False
      end
  | Tbool , Tchar_ _ =>
      match is_true v with
      | Some v => v' = Vchar (if v then 1 else 0)%N
      | _ => False
      end
  | Tnum _ _ , Tbool =>
      match v with
      | Vint v => v' = Vbool (bool_decide (v <> 0))
      | _ => False
      end
  | Tnum _ _ , Tnum sz Unsigned =>
      match v with
      | Vint v => v' = Vint (to_unsigned sz v)
      | _ => False
      end
  | Tnum _ _ , Tnum sz Signed =>
      has_type v (Tnum sz Signed) /\ v' = v
  | Tbool , Tbool => v = v'
  | Tchar_ _ , Tbool =>
      match v with
      | Vchar v => v' = Vbool (bool_decide (v <> 0%N))
      | _ => False
      end
  | Tnum sz sgn , Tchar_ ct =>
      match v with
      | Vint v =>
          v' = Vchar (to_char (bitsN sz) sgn (char_type.bitsN ct) v)
      | _ => False
      end
  | Tchar_ ct , Tnum sz sgn =>
      match v with
      | Vchar v => v' = Vint (of_char (char_type.bitsN ct) (signedness_of_char σ ct) (bitsN sz) sgn v)
      | _ => False
      end
  | Tchar_ ct , Tchar_ ct' =>
      match v with
      | Vchar v => v' = Vchar (to_char (char_type.bitsN ct) Unsigned (char_type.bitsN ct') v)
      | _ => False
      end
  | Tenum _ , _
  | _ , Tenum _ => False (* not reachable due to [underlying_type] *)
  | _ , _ => False
  end.
Arguments conv_int !_ !_ _ _ /.
