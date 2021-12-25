(*
 * Copyright (C) BedRock Systems Inc. 2021
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
Require Import bedrock.prelude.word.zlib.base.
Require Import bedrock.prelude.word.zlib.bit.

#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Equality modulo [n] *)

Module Z.

  Definition eqmod (n x y : Z) : Prop := ∃ i, x = i * n + y.
  #[global] Arguments eqmod : simpl never.

  #[local] Infix "≡{ n }≡" := (eqmod n) : Z_scope.

  Section proper.
    Context (n : Z).
    #[local] Notation "(≡)" := (eqmod n) (only parsing).

    #[global] Instance eqmod_equivalence : Equivalence (≡).
    Proof.
      repeat split; red.
      - by exists 0.
      - intros x y [i->]. exists (-i). lia.
      - intros x y z [i->] [j->]. exists (i+j). lia.
    Qed.

    #[global] Instance eqmod_rewrite_relation : RewriteRelation (≡) := {}.

    #[global] Instance eqmod_add : Proper ((≡) ==> (≡) ==> (≡)) Z.add.
    Proof. intros x1 x2 [i->] y1 y2 [j->]. exists (i+j). lia. Qed.

    #[global] Instance eqmod_opp : Proper ((≡) ==> (≡)) Z.opp.
    Proof. intros x1 x2 [i->]. exists (-i). lia. Qed.

    #[global] Instance eqmod_sub : Proper ((≡) ==> (≡) ==> (≡)) Z.sub.
    Proof. intros x1 x2 [i->] y1 y2 [j->]. exists (i-j). lia. Qed.

    #[global] Instance eqmod_mul : Proper ((≡) ==> (≡) ==> (≡)) Z.mul.
    Proof.
      intros x1 x2 [i->] y1 y2 [j->]. exists (i*j*n + j*x2 + i*y2). lia.
    Qed.
  End proper.

  Lemma eqmod_1 x y : x ≡{1}≡ y.
  Proof. exists (x-y). lia. Qed.
  #[global] Hint Resolve eqmod_1 : core.

  Lemma eqmod_refl2 n x y : x = y → x ≡{n}≡ y.
  Proof. by move=>->. Qed.

  Lemma eqmod_small_eq n x y : x ≡{n}≡ y → 0 ≤ x < n → 0 ≤ y < n → x = y.
  Proof.
    intros [i EQ] Ix Iy. rewrite Z.mul_comm in EQ.
    have := Z.div_unique_pos _ _ _ _ Iy EQ.
    rewrite Z.div_small// =>?. subst i. lia.
  Qed.

  Lemma eqmod_mod_eq n x y : n ≠ 0 → x ≡{n}≡ y → x `mod` n = y `mod` n.
  Proof.
    intros ? [i ->]. by rewrite Z.add_comm Z.mod_add.
  Qed.

  Lemma eqmod_mod n x : n ≠ 0 → x `mod` n ≡{n}≡ x.
  Proof.
    symmetry. exists (x `div` n). by rewrite Z.mul_comm -Z.div_mod.
  Qed.

  Lemma eqmod_divides n m x y : x ≡{n}≡ y → (m | n) → x ≡{m}≡ y.
  Proof. intros [i->] [j->]. exists (i*j). lia. Qed.

  (** [eqmod (2 ^ n)] *)

  Lemma eqmod_bits_eq n x y :
    0 ≤ n →
    (∀ i, 0 ≤ i < n → Z.testbit x i = Z.testbit y i) →
    x ≡{2 ^ n}≡ y.
  Proof.
    move=>Hn. revert x y. pattern n.
    apply: natlike_ind n Hn=>// n ? IH x y Hbits.
    rewrite Z.pow_succ_r// (Z.shift_in_decomp x) (Z.shift_in_decomp y).
    have ->: Z.odd x = Z.odd y.
    { rewrite -!Z.bit0_odd. apply Hbits. lia. }
    have {Hbits}IH : Z.div2 x ≡{2 ^ n}≡ Z.div2 y.
    { apply IH=>i [??]. rewrite -!Z.testbit_succ//. apply Hbits. lia. }
    destruct IH as [k ->]. exists k. rewrite !Z.shift_in_spec. lia.
  Qed.

  Lemma bits_eq_eqmod n x y i :
    0 ≤ n → x ≡{2 ^ n}≡ y → 0 ≤ i < n → Z.testbit x i = Z.testbit y i.
  Proof.
    move=>Hn. revert i x y. pattern n. apply: natlike_ind n Hn; first lia.
    move=>n ? IH i x y [k EQ] [? Hi].
    rewrite Z.pow_succ_r// in EQ. rewrite !(Z.testbit_decomp _ i)//.
    destruct (Z.shift_in_inj (Z.odd x) (Z.div2 x)
      (Z.odd y) (k * 2 ^ n + Z.div2 y)).
    { rewrite (Z.shift_in_decomp x) (Z.shift_in_decomp y) in EQ.
      rewrite EQ !Z.shift_in_spec. lia. }
    case_decide; first done. apply IH; [by exists k|lia].
  Qed.

  (** [Z.le] *)

  Lemma bits_le x y :
    0 ≤ y → (∀ i, 0 ≤ i → Z.testbit x i → Z.testbit y i) → x ≤ y.
  Proof.
    move=>Hy. move: x. pattern y. apply: Z.shift_in_ind y Hy=>[|b y ? IH] x Hxy.
    { suff->: x = 0 by []. apply Z.bits_eq=>i /Hxy{Hxy}.
      rewrite Z.testbit_0_l=>Hx.
      case B: (Z.testbit x i)=>//. case: Hx. by rewrite B. }
    have {IH} Hx : Z.div2 x ≤ y.
    { apply IH=>i Hi Hx. rewrite -(Z.testbit_shift_in_succ b)//.
      apply: Hxy; auto. by rewrite Z.testbit_succ. }
    rewrite (Z.shift_in_decomp x) !Z.shift_in_spec.
    case B1: (Z.odd x); destruct b; simplify_eq/=; auto with lia.
    exfalso. have {Hxy}: Z.testbit (Z.double y) 0 by apply Hxy; auto.
    rewrite Z.bit0_odd Z.double_spec Z.odd_mul andb_True. by case.
  Qed.

End Z.
Infix "≡{ n }≡" := (Z.eqmod n) : Z_scope.
Notation "(≡{ n }≡ )" := (Z.eqmod n) (only parsing) : Z_scope.
