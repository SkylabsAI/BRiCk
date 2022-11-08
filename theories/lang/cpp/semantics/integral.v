
(** * Characterization of "integral types"

    See https://eel.is/c++draft/basic.types#basic.fundamental
 *)
Require Import bedrock.prelude.prelude.
Require Import bedrock.prelude.numbers.
From bedrock.lang.cpp.syntax Require Import types typing translation_unit.
From bedrock.lang.cpp.arith Require Import types operator.

Module Integral.

  (** representation of integral types *)
  Variant t : Set :=
  | Bool
  | Num (_ : bitsize) (_ : signed).


  (** [as_integral tu ty] is the integral representation of the type if one exists.
      In particular, this gets the underlying type of enumerations.
  *)
  Definition as_integral (tu : translation_unit) (ty : type) : option t :=
    match drop_qualifiers ty with
    | Tnum sz sgn => Some $ Num sz sgn
    | Tenum nm =>
        match tu !! nm with
        | Some (Genum ty _) =>
            match ty with
            | Tnum sz sgn => Some $ Num sz sgn
            | Tbool => Some Bool
            | _ => None
            end
        | _ => None
        end
    | Tbool => Some Bool
    | _ => None
    end.

  (** Forgetful function that converts an [Integral.t] to a [type] *)
  Definition to_type (i : t) : type :=
    match i with
    | Bool => Tbool
    | Num sz sgn => Tnum sz sgn
    end.

  (** Casting an integer to the given [Integral.t] *)
  Definition cast (to : Integral.t) (v : Z) : Z :=
    match to with
    | Bool => if bool_decide (v = 0) then 0 else 1
    | Num sz Signed => to_signed sz v
    | Num sz Unsigned => to_unsigned sz v
    end.

  (** Arithmetic promotion
  https://eel.is/c++draft/expr.arith.conv#1.3

  (1.3.1) If both operands have the same type, no further conversion is needed.
  (1.3.2) Otherwise, if both operands have signed integer types or both have
          unsigned integer types, the operand with the type of lesser integer
          conversion rank is converted to the type of the operand with greater
          rank.
  (1.3.3) Otherwise, if the operand that has unsigned integer type has rank
          greater than or equal to the rank of the type of the other operand,
          the operand with signed integer type is converted to the type of the
          operand with unsigned integer type.
  (1.3.4) Otherwise, if the type of the operand with signed integer type can
          represent all of the values of the type of the operand with unsigned
          integer type, the operand with unsigned integer type is converted to
          the type of the operand with signed integer type.
  (1.3.5) Otherwise, both operands are converted to the unsigned integer type
          corresponding to the type of the operand with signed integer type.
  *)
  Definition promote_integral (ty1 ty2 : Integral.t) : Integral.t :=
    match ty1 , ty2 with
    | Bool , x => x
    | x , Bool => x
    | Num sz1 sgn1 , Num sz2 sgn2 =>
        if bool_decide (sgn1 = sgn2) then
          Num (bitsize_max sz1 sz2) sgn1
        else
          let (ssz, usz) := match sgn1 with
                            | Signed => (sz1, sz2)
                            | Unsigned => (sz2, sz1)
                            end
          in
          if bool_decide (bitsize_le ssz usz) then
            Num usz Unsigned
          else if bool_decide (bitsN ssz > bitsN usz)%Z then
            (** ^^^ it is odd that [N] comparisons do not work. *)
            Num ssz Signed
          else
            Num ssz Unsigned
    end.

End Integral.
