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
    else Z.to_N $ to_unsigned_bits to_bits v
  else Z.to_N $ to_unsigned_bits to_bits v.

Definition of_char (from_bits : N) (from_sgn : signed) (to_bits : N) (to_sgn : signed) (n : N) : Z :=
  (* first we need to sign extend using frm_sgn *)
  let n : Z :=
    if from_sgn is Signed then
      if bool_decide (n < 2^(from_bits-1)) then n else to_signed_bits from_bits n
    else n in
  if to_sgn is Signed then to_signed_bits to_bits n else to_unsigned_bits to_bits n.

(* suppose that you are in an architecture with unsigned characters
    and you wrote (128)
  *)

Succeed Example TEST : of_char 8 Signed 32 Signed 1 = 1 := eq_refl.
Succeed Example TEST : of_char 8 Signed 32 Signed 128 = -128 := eq_refl.
Succeed Example TEST : of_char 8 Signed 32 Signed 127 = 127 := eq_refl.
Succeed Example TEST : of_char 8 Signed 16 Unsigned 128 = 65408 := eq_refl.
Succeed Example TEST : of_char 32 Signed 8 Signed 256 = 0 := eq_refl.
Succeed Example TEST : of_char 32 Signed 8 Signed 128 = -128 := eq_refl.
Succeed Example TEST : of_char 32 Signed 16 Signed 128 = 128 := eq_refl.
Succeed Example TEST : of_char 16 Signed 8 Unsigned 128 = 128 := eq_refl.

(* Other tests *)
Succeed Example TEST : of_char 8 Signed 8 Unsigned 128 = 128 := eq_refl.
Succeed Example TEST : of_char 16 Signed 8 Unsigned 128 = 128 := eq_refl.

Succeed Example TEST : of_char 8 Signed 8 Signed 128 = -128 := eq_refl.
Succeed Example TEST : of_char 8 Signed 8 Signed 129 = -127 := eq_refl.

Succeed Example TEST : of_char 16 Signed 8 Signed 128 = -128 := eq_refl.
Succeed Example TEST : of_char 16 Signed 8 Signed 129 = -127 := eq_refl.

Succeed Example TEST : of_char 8 Unsigned 8 Signed 129 = -127 := eq_refl.
Succeed Example TEST : of_char 16 Unsigned 8 Signed 129 = -127 := eq_refl.

Succeed Example TEST : of_char 8 Unsigned 8 Signed 128 = -128 := eq_refl.
Succeed Example TEST : of_char 8 Unsigned 16 Signed 128 = 128 := eq_refl.

(* END TODO move to syntax *)

(** Numeric conversions.

    This includes both conversions and promotions between fundamental
    numeric types and enumerations (which have underlying fundamental
    types).

    This relation only holds on well-typed values, see [conv_int_well_typed].
  *)
Definition conv_int {σ : genv} (tu : translation_unit) (from to : type) (v v' : val) : Prop :=
  has_type v from /\
  match underlying_unqual_type tu from , underlying_unqual_type tu to with
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
  | _ , Tenum _ (* not reachable due to [underlying_unqual_type] *)
  | _ , _ => False
  end.
Arguments conv_int !_ !_ _ _ /.

Section conv_int.
  Context `{Hmod : tu ⊧ σ}.

  Lemma conv_int_well_typed ty ty' v v' :
       tu ⊧ σ -> (* TODO only needed if either type is a [Tenum] *)
       conv_int tu ty ty' v v' ->
       has_type v ty /\ has_type v' ty'.
  Proof.
  (* TODO -- prove this
    rewrite /conv_int;
    destruct (underlying_type tu ty) eqn:src_ty; rewrite /=; try tauto;
    destruct (underlying_type tu ty') eqn:dst_ty; rewrite /=; try tauto;
    intuition.
    { case_match.
      { destruct H2. subst. }

    { } *)
  Admitted.

  (* Note that a no-op conversion on a raw value is not permitted. *)
  Lemma conv_int_num_id sz sgn v :
    let ty := Tnum sz sgn in
    ~(exists r, v = Vraw r) ->
    has_type v ty ->
    conv_int tu ty ty v v.
  Proof using Hmod.
    rewrite /=/conv_int/underlying_type/=.
    intros. split; eauto.
    destruct sgn. split; eauto.
    apply has_int_type' in H0.
    destruct H0.
    - destruct H0 as [?[??]].
      subst.
      revert H1.
      rewrite /bound/min_val/max_val.
      intros.
      rewrite to_unsigned_id; eauto.
      destruct sz; simpl; try lia.
    - exfalso. apply H. destruct H0 as [?[??]]. eauto.
  Qed.

  (* conversion is deterministic *)
  Lemma conv_int_unique : forall from to v,
      forall v' v'', conv_int tu from to v v' ->
                conv_int tu from to v v'' ->
                v' = v''.
  Proof using Hmod.
    (* TODO -- prove this *)
  Admitted.
End conv_int.

(* This (effectively) lifts [conv_int] to arbitrary types.

   TODO: it makes sense for this to mirror the properties of [conv_int], but
   pointer casts require side-conditions that are only expressible in
   separation logic.
 *)
Definition convert {σ : genv} (tu : translation_unit) (from to : type) (v : val) (v' : val) : Prop :=
  if is_pointer from && bool_decide (erase_qualifiers from = erase_qualifiers to) then
    (* TODO: this conservative *)
    has_type v from /\ has_type v' to /\ v' = v
  else if is_arithmetic from && is_arithmetic to then
    conv_int tu from to v v'
  else False.
