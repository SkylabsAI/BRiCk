(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.word.base.
Require Import bedrock.prelude.word.num.
Require Import bedrock.prelude.word.aux_arg.
Require Import bedrock.prelude.word.zify.
Require Import bedrock.prelude.word.type.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Concrete word types *)
(** Overview:

- [WORD_ZIFY_NUM] mixin teaching zify about number notation regardless
of [Zify.zify_convert_to_euclidean_division_equations_flag]

- [WORD_AUX] bundle zify, number notation mixins to ease application

- [wN] applications of [WORD_AUX] to type [word N] (for a few values
of [N])

- [notation] module defining notation scopes [%iN], [%uN] (for a few
values of [N]) parsing numbers of type [word N] with signed, unsigned
bounds checks, as well as scopes [%xN] analogous to [%uN] but printing
(when opened) in hexadecimal rather than decimal

TODO (PDS): Talk to Janno. We _override_ [Zify.zify_post_hook] but
should be able to (somewhat) modularly _extend_ it.

*)

(** Teach [zify] about number notation *)

Module Type WORD_ZIFY_NUM
  (Import WT : WORD_TYPE)
  (Import WM : WORD_MODULUS WT)
  (Import WS : WORD_MIN_SIGNED WT)
  (Import Wz : WORD_ZIFY WT WM)
  (WN : WORD_NUM WT).

  Import Coq.micromega.ZifyClasses.

  Import base.word.

  (**
  Replace numbers [to_Z (WN.of_Z z)], by [z], [z+m], or [z `mod` m]
  depending on bounds checks. Typically, [WN.of_Z] arises from number
  notation, ensuring [z] is a numeral that is in bounds for either [z]
  or [z+m].

  Note: The following zify instance assumes post-zify simplification
  (and that [Z.leb], [Z.ltb] are not marked [simpl never]) to
  eliminate lingering case distinctions. For occurrences of [WN.of_Z]
  arising from number notation, this results in simpler goals compared
  to using an [UnOpSpec litZ] instance.
  *)

  Definition litZ (z : Z) : Z :=
    if (0 <=? z) && (z <? m) then z
    else if (ms <=? z) && (z <? 0) then z + m
    else z `mod` m.

  Lemma zify_lit_inj z : to_Z (WN.of_Z z) = Reduce (litZ z).
  Proof.
    rewrite WN.of_Z_spec ms_spec m_spec to_of_Z_modulo
      modulus_half_modulus. set h := half_modulus _.
    case Hu: (_ && _); [|case Hs: (_ && _)].
    - rewrite Z.mod_small//. lia.
    - rewrite -(Z.mod_small (Z.add _ _) (2 * h)); last lia.
      rewrite Z.add_mod; last lia. rewrite Z.mod_same; last lia.
      rewrite Z.add_0_r Z.mod_mod//. lia.
    - done.
  Qed.

  #[global] Program Instance zify_lit : UnOp WN.of_Z := {|
    TUOp := Reduce litZ;
    TUOpInj := zify_lit_inj;
  |}.
  Add Zify UnOp zify_lit.

End WORD_ZIFY_NUM.

(** Simplify after [zify] for [WORD_ZIFY_NUM] *)

Ltac word_zify_num_post := cbn in *.
Ltac Zify.zify_post_hook ::= word_zify_num_post.

(** Bundle [WORD_NUM], [WORD_ZIFY], [WORD_ZIFY_NUM] *)

Module Type WORD_AUX
  (WT : WORD_TYPE)
  (WM : WORD_MODULUS WT)
  (WS : WORD_MIN_SIGNED WT)
:= WORD_NUM WT
<+ WORD_ZIFY WT WM
<+ WORD_ZIFY_NUM WT WM WS.

(** [word 8] *)

Module w8.
  Definition W : wordT := word_S 7.

  Definition m : Z := Evaluate (word.modulus W).
  Lemma m_spec : m = word.modulus W.
  Proof. done. Qed.

  Definition ms : Z := Evaluate (- word.half_modulus W).
  Lemma ms_spec : ms = - word.half_modulus W.
  Proof. done. Qed.

  Include WORD_AUX.
End w8.

(** [word 16] *)

Module w16.
  Definition W : wordT := word_S 15.

  Definition m : Z := Evaluate (word.modulus W).
  Lemma m_spec : m = word.modulus W.
  Proof. done. Qed.

  Definition ms : Z := Evaluate (- word.half_modulus W).
  Lemma ms_spec : ms = - word.half_modulus W.
  Proof. done. Qed.

  Include WORD_AUX.
End w16.

(** [word 32] *)

Module w32.
  Definition W : wordT := word_S 31.

  Definition m : Z := Evaluate (word.modulus W).
  Lemma m_spec : m = word.modulus W.
  Proof. done. Qed.

  Definition ms : Z := Evaluate (- word.half_modulus W).
  Lemma ms_spec : ms = - word.half_modulus W.
  Proof. done. Qed.

  Include WORD_AUX.
End w32.

(** [word 64] *)

Module w64.
  Definition W : wordT := word_S 63.

  Definition m : Z := Evaluate (word.modulus W).
  Lemma m_spec : m = word.modulus W.
  Proof. done. Qed.

  Definition ms : Z := Evaluate (- word.half_modulus W).
  Lemma ms_spec : ms = - word.half_modulus W.
  Proof. done. Qed.

  Include WORD_AUX.
End w64.

(** [word 128] *)

Module w128.
  Definition W : wordT := word_S 127.

  Definition m : Z := Evaluate (word.modulus W).
  Lemma m_spec : m = word.modulus W.
  Proof. done. Qed.

  Definition ms : Z := Evaluate (- word.half_modulus W).
  Lemma ms_spec : ms = - word.half_modulus W.
  Proof. done. Qed.

  Include WORD_AUX.
End w128.

(** Number notation for all of the above *)

Module Import notation.

  (** [word 8] *)

  Declare Scope x8_scope.
  Delimit Scope x8_scope with x8.
  Number Notation word w8.uparse w8.xprint
    (via w8.num mapping [w8.of_Z => w8.Num]) : x8_scope.

  Declare Scope u8_scope.
  Delimit Scope u8_scope with u8.
  Number Notation word w8.uparse w8.dprint
    (via w8.num mapping [w8.of_Z => w8.Num]) : u8_scope.

  Declare Scope i8_scope.
  Delimit Scope i8_scope with i8.
  Number Notation word w8.sparse w8.dprint
    (via w8.num mapping [w8.of_Z => w8.Num]) : i8_scope.

  (** [word 16] *)

  Declare Scope x16_scope.
  Delimit Scope x16_scope with x16.
  Number Notation word w16.uparse w16.xprint
    (via w16.num mapping [w16.of_Z => w16.Num]) : x16_scope.

  Declare Scope u16_scope.
  Delimit Scope u16_scope with u16.
  Number Notation word w16.uparse w16.dprint
    (via w16.num mapping [w16.of_Z => w16.Num]) : u16_scope.

  Declare Scope i16_scope.
  Delimit Scope i16_scope with i16.
  Number Notation word w16.sparse w16.dprint
    (via w16.num mapping [w16.of_Z => w16.Num]) : i16_scope.

  (** [word 32] *)

  Declare Scope x32_scope.
  Delimit Scope x32_scope with x32.
  Number Notation word w32.uparse w32.xprint
    (via w32.num mapping [w32.of_Z => w32.Num]) : x32_scope.

  Declare Scope u32_scope.
  Delimit Scope u32_scope with u32.
  Number Notation word w32.uparse w32.dprint
    (via w32.num mapping [w32.of_Z => w32.Num]) : u32_scope.

  Declare Scope i32_scope.
  Delimit Scope i32_scope with i32.
  Number Notation word w32.sparse w32.dprint
    (via w32.num mapping [w32.of_Z => w32.Num]) : i32_scope.

  (** [word 64] *)

  Declare Scope x64_scope.
  Delimit Scope x64_scope with x64.
  Number Notation word w64.uparse w64.xprint
    (via w64.num mapping [w64.of_Z => w64.Num]) : x64_scope.

  Declare Scope u64_scope.
  Delimit Scope u64_scope with u64.
  Number Notation word w64.uparse w64.dprint
    (via w64.num mapping [w64.of_Z => w64.Num]) : u64_scope.

  Declare Scope i64_scope.
  Delimit Scope i64_scope with i64.
  Number Notation word w64.sparse w64.dprint
    (via w64.num mapping [w64.of_Z => w64.Num]) : i64_scope.

  (** [word 128] *)

  Declare Scope x128_scope.
  Delimit Scope x128_scope with x128.
  Number Notation word w128.uparse w128.xprint
    (via w128.num mapping [w128.of_Z => w128.Num]) : x128_scope.

  Declare Scope u128_scope.
  Delimit Scope u128_scope with u128.
  Number Notation word w128.uparse w128.dprint
    (via w128.num mapping [w128.of_Z => w128.Num]) : u128_scope.

  Declare Scope i128_scope.
  Delimit Scope i128_scope with i128.
  Number Notation word w128.sparse w128.dprint
    (via w128.num mapping [w128.of_Z => w128.Num]) : i128_scope.

End notation.

Section examples.
  Import word.const word.add.

  (** bounds in [%i8] *)
  Fail Check (-129)%i8.
  Check (-128)%i8.
  Check 127%i8.
  Fail Check 128%i8.

  (** bounds in [%u8] *)
  Fail Check (-1)%u8.
  Check 0%u8.
  Check 255%u8.
  Fail Check 256%u8.

  (** hex parsing *)
  Goal word.to_Z (-0x1)%i8 = 255.
  Proof. done. Abort.
  Goal word.signed 0xFF%u8 = -1.
  Proof. done. Abort.
  Goal (-0x1)%i8 = 0xFF%u8.
  Proof. done. Abort.

  (** hex printing *)
  Section hex.
    Open Scope x8.

    Fail Check -1.
    Goal word.signed 0xFF = (-1)%Z.
    Proof. done. Abort.
    Goal word.to_Z 0xFF = 255%Z.
    Proof. done. Abort.
  End hex.

  (** multi-type printing *)
  Goal word.to_Z (-1)%i16 = word.to_Z 0xFFFF%i32.
  Proof. done. Abort.

  (** [WORD_ZIFY] *)

  Local Open Scope word_scope.

  Implicit Types x y : word 8.

  Goal ∀ x, x = x.
  Proof. zify. Abort.
  (*
  x : word 8
  cstr : 0 ≤ word.to_Z x < 256
  ______________________________________
  word.to_Z x = word.to_Z x
  *)
  Goal ∀ x, x = x.
  Proof. lia. Abort.

  Goal ∀ x, x = x + 1 - 1.
  Proof. zify. Abort.
  (**
  x : word 8
  cstr : 0 ≤ word.to_Z x < 256
  z0 : Z
  H0 : word.to_Z x + 1 < 256 ∧ z0 = (word.to_Z x + 1)%Z
       ∨ 256 ≤ word.to_Z x + 1 ∧ z0 = (word.to_Z x + 1 - 256)%Z
  z1 : Z
  H1 : z0 - 1 < 0 ∧ z1 = (z0 - 1 + 256)%Z ∨ 0 ≤ z0 - 1 ∧ z1 = (z0 - 1)%Z
  ______________________________________
  word.to_Z x = z1
  *)
  Goal ∀ x, x = x + 1 - 1.
  Proof. lia. Abort.

  (** [WORD_ZIFY_NUM] *)

  Goal 1 = 1%i8.
  Proof. zify. Abort.
  (**
  ______________________________________
  1 = 1
  *)
  Goal 1 = 1%i8.
  Proof. lia. Abort.

  Goal (-1)%i8 = 255%u8.
  Proof. zify. Abort.
  (**
  ______________________________________
  (-1 + 256)%Z = 255
  *)
  Goal (-1)%i8 = 255%u8.
  Proof. lia. Abort.

  Goal (-1)%W = 255%u8.
  Proof. zify. Abort.
  (**
  ______________________________________
  (256 - 1)%Z = 255
  *)
  Goal (-1)%W = 255%u8.
  Proof. lia. Abort.

End examples.
