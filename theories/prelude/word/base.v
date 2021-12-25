(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code written (and not distributed) by
 * David Swasey:
 *
 *	Copyright 2017 by David Swasey
 *
 *	SPDX-License-Identifier: LGPL-2.1-or-later
 *
 * Swasey had derived his code from code original to the CompCert
 * verified compiler. That original code is
 *
 *	Copyright by Institut National de Recherche en Informatique et
 *	en Automatique (INRIA) and AbsInt Angewandte Informatik GmbH
 *
 * and used according to the GNU Lesser General Public License v2.1 or
 * later.
 *
 *	SPDX-License-Identifier: LGPL-2.1-or-later
 *
 * Original Code:
 * https://github.com/AbsInt/CompCert/blob/04f499c632a76e460560fc9ec4e14d8216e7fc18/lib/Integers.v
 *
 * Original License:
 * https://github.com/AbsInt/CompCert/blob/04f499c632a76e460560fc9ec4e14d8216e7fc18/LICENSE
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.prelude.word.zlib.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Axiomatization of [n]-bit words *)
(** We axiomatize types [W : wordT] of twos-complement numbers and
develop a small theory of:

- [word.bitsize W : Z] size of words of type [W]

- [word.modulus W : Z ≈ 2 ^ word.bitsize W]

- [word.half_modulus W : Z ≈ word.modulus `div` 2]

- [word.of_Z (z : Z) : W] represents the integer [z `mod` word.modulus
W] in type [W]

- [word.to_Z (x : W) : Z] interprets word [x] as an integer satisfying
[0 ≤ word.to_Z x < word.modulus W]

- [word.signed (x : W) : Z] interprets word [x] as an integer
satisfying [- half_modulus W ≤ word.signed x < word.half_modulus W]

- [word.testbit (x : W) (i : Z) : bool] for expressing bitwise specs

We use operational type classes and canonical structures (as opposed
to Coq functors) so that we can uniformly define operations that
convert between words of various sizes. Elsewhere, we give an
efficient implementation of the word axioms. *)

Declare Scope word_scope.
Delimit Scope word_scope with W.

Module word.

  (**
  The bit width of inhabitants of a word type.

  Note: Except were necessary, we prefer the following [bitsize W :
  Z].
  *)
  Class BitsizeNat (W : Set) : Set := bitsize_nat : nat.
  #[global] Hint Mode BitsizeNat ! : typeclass_instances.
  #[global] Arguments bitsize_nat _ {_} : simpl never, assert.

  (**
  The function [to_Z] interprets a word as an unsigned integer.
  *)
  Class ToZ (W : Set) : Set := to_Z : W → Z.
  #[global] Hint Mode ToZ ! : typeclass_instances.
  #[global] Arguments to_Z {_ _} _%W : simpl never, assert.

  (**
  The function [of_Z] computes the word representing an integer,
  treating its argument modulo [2 ^ n].
  *)
  Class OfZ (W : Set) : Set := of_Z : Z → W.
  #[global] Hint Mode OfZ ! : typeclass_instances.
  #[global] Arguments of_Z _ {_} _ : simpl never, assert.
  #[global] Instance: Params (@of_Z) 2 := {}.

  (**
  We use canonical structures to enable unification to find a word
  type's bit size and other data. We cannot key canonical structure
  inference on the bit size itself, because all word types would then
  share the single key [S].
  *)

  Record WordMixin (W : Set) `{BitsizeNat W, ToZ W, OfZ W} : Prop := {
    mixin_bitsize_nat_nonzero : bitsize_nat W ≠ 0%nat;
    mixin_to_Z_range (x : W) : 0 ≤ to_Z x < 2 ^ Z.of_nat (bitsize_nat W);
    mixin_to_of_Z_modulo z :
      to_Z (of_Z W z) = z `mod` 2 ^ Z.of_nat (bitsize_nat W);
    mixin_of_to_Z x : of_Z W (to_Z x) = x;
  }.

  Structure wordT : Type := WordT {
    word_car :> Set;
    word_bitsize_nat : BitsizeNat word_car;
    word_to_Z : ToZ word_car;
    word_of_Z : OfZ word_car;
    word_mixin : WordMixin word_car;
  }.

  Add Printing Constructor wordT.
  #[global] Arguments WordT {_ _ _ _} _ : assert.
  #[global] Hint Extern 0 (word.BitsizeNat _) =>
    refine (word_bitsize_nat _); shelve : typeclass_instances.
  #[global] Hint Extern 0 (word.ToZ _) =>
    refine (word_to_Z _); shelve : typeclass_instances.
  #[global] Hint Extern 0 (word.OfZ _) =>
    refine (word_of_Z _); shelve : typeclass_instances.
  Arguments word_car : simpl never.
  Arguments word_bitsize_nat : simpl never.
  Arguments word_to_Z : simpl never.
  Arguments word_of_Z : simpl never.
  Arguments word_mixin : simpl never.

  #[global] Bind Scope word_scope with word_car.

  Definition mixin_of' W {Wc : wordT} (f : Wc → W)
    : WordMixin Wc := word_mixin Wc.
  #[local] Notation id := (fun x => x) (only parsing).
  Notation mixin_of W := (Hnf (mixin_of' W id)) (only parsing).
  Notation type_of W := (WordT (mixin_of W)) (only parsing).

  (**
  Side-condition on [bitsize_nat W] relevant to the theory of a few word
  operations.
  *)
  Class BitsizeAtLeast (W : wordT) (n : nat) : Prop :=
    bitsize_nat_at_least : (n ≤ bitsize_nat W)%nat.
  #[global] Hint Mode BitsizeAtLeast + + : typeclass_instances.
  #[global] Arguments bitsize_nat_at_least _ _ {_} : assert.

  (**
  Some constants relevant to words. We define these for efficient
  computation rather than readability.
  *)
  Definition bitsize (W : wordT) : Z := Z.of_nat (bitsize_nat W).
  Definition modulus (W : wordT) : Z := two_power_nat (bitsize_nat W).
  Definition half_modulus (W : wordT) : Z := Z.div2 (modulus W).

  #[global] Arguments bitsize : simpl never.
  #[global] Arguments modulus : simpl never.
  #[global] Arguments half_modulus : simpl never.

  (**
  Sets of integers representable without loss. Meant to be unfolded.
  *)
  Definition is_unsigned (W : wordT) (z : Z) : Prop :=
    0 ≤ z < modulus W.
  Definition is_signed (W : wordT) (z : Z) : Prop :=
    let h := half_modulus W in - h ≤ z < h.

  (**
  The function [signed] interprets a word as a signed twos-complement
  number.
  *)
  Definition signed {W : wordT} (x : W) : Z :=
    let z := to_Z x in
    let m := modulus W in
    if decide (z < Z.div2 m) then z else z - m.

  (**
  The function [testbit x i] returns the [i]th bit in word [x].
  *)
  Definition testbit {W : wordT} (x : W) (i : Z) : bool :=
    Z.testbit (to_Z x) i.

  #[global] Arguments signed : simpl never.
  #[global] Arguments testbit : simpl never.

  Implicit Types W : wordT.

  (** [bitsize_nat], [bitsize] *)

  Lemma bitsize_nat_nonzero W : bitsize_nat W ≠ 0%nat.
  Proof. apply (mixin_bitsize_nat_nonzero _ (word_mixin W)). Qed.

  Lemma bitsize_nat_inv W : ∃ n, bitsize_nat W = S n.
  Proof.
    have := bitsize_nat_nonzero W. by destruct (bitsize_nat W); eauto.
  Qed.

  Lemma bitsize_inv W : ∃ n, bitsize W = Z.succ n ∧ 0 ≤ n.
  Proof.
    rewrite /bitsize. have [n ->] := bitsize_nat_inv W.
    eexists. by rewrite Nat2Z.inj_succ.
  Qed.

  Lemma bitsize_at_least W n `{!BitsizeAtLeast W n} : Z.of_nat n ≤ bitsize W.
  Proof. by apply Nat2Z.inj_le, bitsize_nat_at_least. Qed.

  Lemma bitsize_min W : 1 ≤ bitsize W.
  Proof. rewrite /bitsize. have := bitsize_nat_nonzero W. lia. Qed.
  #[global] Hint Resolve bitsize_min : core.

  Lemma bitsize_nonneg W : 0 ≤ bitsize W.
  Proof. have := bitsize_min W. lia. Qed.
  #[global] Hint Resolve bitsize_nonneg : core.

  Lemma bitsize_pos W : 0 < bitsize W.
  Proof. have := bitsize_min W. lia. Qed.
  #[global] Hint Resolve bitsize_pos : core.

  (** [modulus] *)

  Lemma modulus_bitsize W : modulus W = 2 ^ bitsize W.
  Proof. rewrite/modulus/bitsize. by rewrite two_power_nat_equiv. Qed.

  Lemma bitsize_lt_modulus W : bitsize W < modulus W.
  Proof. rewrite modulus_bitsize. exact: Z.pow2_strict. Qed.

  Lemma modulus_min W : 2 ≤ modulus W.
  Proof.
    rewrite modulus_bitsize -{1}(Z.pow_1_r 2). exact: Z.pow_le_mono_r.
  Qed.

  Lemma modulus_nonzero W : modulus W ≠ 0.
  Proof. have := modulus_min W. lia. Qed.
  #[global] Hint Resolve modulus_nonzero : core.

  Lemma modulus_pos W : 0 < modulus W.
  Proof. have := modulus_min W. lia. Qed.
  #[global] Hint Resolve modulus_pos : core.

  (** [half_modulus] *)

  Lemma half_modulus_modulus W : half_modulus W = modulus W `div` 2.
  Proof. rewrite /half_modulus. by rewrite Z.div2_div. Qed.

  Lemma half_modulus_bitsize W : half_modulus W = 2 ^ (bitsize W - 1).
  Proof.
    rewrite half_modulus_modulus modulus_bitsize.
    by rewrite -Z.div2_div Z.div2_pow2.
  Qed.

  Lemma bitsize_le_half_modulus W : bitsize W ≤ half_modulus W.
  Proof.
    rewrite half_modulus_bitsize Z.log2_up_le_pow2//.
    have := Z.log2_up_lt_lin (bitsize W) ltac:(done). lia.
  Qed.

  Lemma modulus_half_modulus W : modulus W = 2 * half_modulus W.
  Proof.
    rewrite half_modulus_modulus. apply Z.div_exact; first done.
    by rewrite modulus_bitsize Z.pow2_mod2.
  Qed.

  Lemma half_modulus_min W : 1 ≤ half_modulus W.
  Proof. have := modulus_min W. rewrite modulus_half_modulus. lia. Qed.

  Lemma half_modulus_nonzero W : half_modulus W ≠ 0.
  Proof. have := half_modulus_min W. lia. Qed.
  #[global] Hint Resolve half_modulus_nonzero : core.

  Lemma half_modulus_pos W : 0 < half_modulus W.
  Proof. have := half_modulus_min W. lia. Qed.
  #[global] Hint Resolve half_modulus_pos : core.

  Section mixin.
    Context {W : wordT}.
    Implicit Types (x : W).

    Lemma to_Z_range x : Reduce (is_unsigned W (to_Z x)).
    Proof.
      rewrite modulus_bitsize.
      apply (mixin_to_Z_range _ (word_mixin W)).
    Qed.

    Lemma to_of_Z_modulo z : to_Z (of_Z W z) = z `mod` modulus W.
    Proof.
      rewrite modulus_bitsize.
      apply (mixin_to_of_Z_modulo _ (word_mixin W)).
    Qed.

    Lemma of_to_Z x : of_Z W (to_Z x) = x.
    Proof. apply (mixin_of_to_Z _ (word_mixin W)). Qed.
  End mixin.
  #[global] Hint Resolve to_Z_range of_to_Z : core.

  Section theory.
    Context {W : wordT}.
    Implicit Types (x y : W) (z : Z).
    #[local] Infix "≡" := (Z.eqmod (modulus W)) (only parsing).
    #[local] Notation "(≡)" := (Z.eqmod (modulus W)) (only parsing).

    #[global] Instance to_Z_inj : Inj (@eq W) (=) to_Z.
    Proof. move=>x y H. by rewrite -(of_to_Z x) -(of_to_Z y) H. Qed.

    #[global] Instance word_inhabited : Inhabited W.
    Proof. exact (populate (of_Z _ 0)). Qed.

    #[global] Instance word_eq_dec : EqDecision W := inj_eq_dec to_Z.

    (** In fact, [W] is a finite type (see ./finite.v). *)
    #[global] Instance word_countable : Countable W :=
      inj_countable' _ _ of_to_Z.

    (** [of_Z] *)

    #[global] Instance of_Z_proper : Proper ((≡) ==> (=)) (of_Z W).
    Proof.
      intros z1 z2 ?. apply (inj to_Z). rewrite !to_of_Z_modulo.
      exact: Z.eqmod_mod_eq.
    Qed.

    #[global] Instance of_Z_surj : Surj (=) (of_Z W).
    Proof. move=>x. by exists (to_Z x). Qed.

    Lemma of_Z_eq z y : z ≡ to_Z y → of_Z W z = y.
    Proof. by intros ->. Qed.

    (** [to_Z] *)

    (**
    Higher cost than [to_Z_inj], which is more frequently useful.
    *)
    #[global] Instance to_Z_inj_eqmod : Inj (@eq W) (≡) to_Z | 10.
    Proof. move=>x y H. by rewrite -(of_to_Z x) -(of_to_Z y) H. Qed.

    Lemma to_of_Z z : Reduce (is_unsigned W z) → to_Z (of_Z W z) = z.
    Proof. intros. by rewrite to_of_Z_modulo Z.mod_small. Qed.

    Lemma to_of_Z_eqmod z : to_Z (of_Z W z) ≡ z.
    Proof. by rewrite to_of_Z_modulo Z.eqmod_mod. Qed.

    Lemma to_Z_min x : 0 ≤ to_Z x.
    Proof. by destruct (to_Z_range x). Qed.
    #[local] Hint Resolve to_Z_min : core.

    Lemma to_Z_max x : to_Z x < modulus W.
    Proof. by destruct (to_Z_range x). Qed.
    #[local] Hint Resolve to_Z_max : core.

    Lemma to_Z_half_modulus x : to_Z x < 2 * half_modulus W.
    Proof. by rewrite -modulus_half_modulus. Qed.

    (** [signed] *)

    Lemma signed_to_Z x : signed x ≡ to_Z x.
    Proof. rewrite /signed. case_decide. done. exists (-1)%Z; lia. Qed.

    Lemma of_Z_signed x : of_Z W (signed x) = x.
    Proof. by rewrite -[RHS](of_to_Z x) signed_to_Z. Qed.

    #[global] Instance signed_inj : Inj (@eq W) (=) signed.
    Proof. move=>x y H. by rewrite -(of_Z_signed x) -(of_Z_signed y) H. Qed.

    (**
    Higher cost than [signed_inj], which is more frequently useful.
    *)
    #[global] Instance signed_inj_eqmod : Inj (@eq W) (≡) signed | 10.
    Proof. move=>x y H. by rewrite -(of_Z_signed x) -(of_Z_signed y) H. Qed.

    Lemma signed_of_Z_eqmod z : signed (of_Z W z) ≡ z.
    Proof. by rewrite signed_to_Z to_of_Z_eqmod. Qed.

    Lemma signed_of_Z z : Reduce (is_signed W z) → signed (of_Z W z) = z.
    Proof.
      intros. rewrite/signed. case: (decide (0 ≤ z))=>?.
      - rewrite (to_of_Z z) modulus_half_modulus; last lia.
        rewrite decide_True// Z.div2_div Z.mul_comm Z.div_mul//. lia.
      - set z' := z + modulus W. have->: of_Z W z = of_Z W z'.
        { apply of_Z_eq. rewrite to_of_Z_eqmod.
          symmetry. exists 1. rewrite/z'. lia. }
        rewrite Z.div2_div (to_of_Z z') {}/z' modulus_half_modulus;
          last lia.
        rewrite decide_False; first lia.
        rewrite Z.mul_comm Z.div_mul//. lia.
    Qed.

    Lemma signed_range x : Reduce (is_signed W (signed x)).
    Proof.
      rewrite/signed -/(half_modulus W). have := to_Z_range x.
      rewrite modulus_half_modulus. case_decide; lia.
    Qed.

    Lemma signed_min x : - half_modulus W ≤ signed x.
    Proof. by destruct (signed_range x). Qed.

    Lemma signed_max x : signed x < half_modulus W.
    Proof. by destruct (signed_range x). Qed.

    (** [testbit] *)

    Lemma testbit_of_Z z i :
      0 ≤ i < bitsize W → testbit (of_Z W z) i = Z.testbit z i.
    Proof.
      apply Z.bits_eq_eqmod; auto.
      by rewrite -modulus_bitsize to_of_Z_eqmod.
    Qed.

    Lemma bits_eq x y :
      (∀ i, 0 ≤ i < bitsize W → testbit x i = testbit y i) → x = y.
    Proof.
      intros. rewrite -(of_to_Z x) -(of_to_Z y).
      apply of_Z_proper. rewrite modulus_bitsize. exact: Z.eqmod_bits_eq.
    Qed.

    Lemma bits_above x i : bitsize W ≤ i → testbit x i = false.
    Proof. apply Z.bits_above; auto. by rewrite -modulus_bitsize. Qed.

    Lemma bits_le x y :
      (∀ i, 0 ≤ i < bitsize W → testbit x i → testbit y i) →
      to_Z x ≤ to_Z y.
    Proof.
      intros Hxy. apply Z.bits_le; auto=>i Hi Hx.
      destruct (decide (i < bitsize W)).
      - by apply: Hxy Hx.
      - rewrite -/(testbit x i) bits_above// in Hx. lia.
    Qed.

    Lemma sign_bit_to_Z x :
      testbit x (bitsize W - 1) =
      negb (bool_decide (to_Z x < half_modulus W)).
    Proof.
      rewrite half_modulus_bitsize. destruct (bitsize_inv W) as (n & Hn & ?).
      rewrite Hn Z.sub_1_r Z.pred_succ.
      apply Z.sign_bit; first done. by rewrite -Hn -modulus_bitsize.
    Qed.

    Lemma bits_signed x i :
      0 ≤ i →
      Z.testbit (signed x) i =
      testbit x $ let n := bitsize W in if decide (i < n) then i else n - 1.
    Proof.
      intros Hi. cbn zeta. case_decide.
      { apply (Z.bits_eq_eqmod (bitsize W)); auto.
        by rewrite -modulus_bitsize signed_to_Z. }
      rewrite /signed sign_bit_to_Z. case_bool_decide.
      - rewrite decide_True//=.
        apply (Z.bits_above (bitsize W)); [done| |lia].
        by rewrite -modulus_bitsize.
      - rewrite decide_False//=.
        apply (Z.bits_above_neg (bitsize W)); [done| |lia].
        rewrite -modulus_bitsize. have := to_Z_range x. lia.
    Qed.

  End theory.
  #[global] Hint Opaque
    to_Z of_Z signed
  : typeclass_instances.
  #[global] Hint Resolve
    to_of_Z_eqmod
    to_Z_min
    to_Z_max
    signed_to_Z
    of_Z_signed
    signed_of_Z_eqmod
    signed_min
    signed_max
  : core.

End word.
Export word(WordMixin,wordT,WordT).
Add Printing Constructor wordT.
Coercion word.word_car : wordT >-> Sortclass.
