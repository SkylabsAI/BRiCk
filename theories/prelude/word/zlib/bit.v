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
Require Import bedrock.prelude.word.zlib.pow2.

#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Bitwise reasoning *)
(** Overview:

- [shift_in (b : bool) (z : Z) : Z] is the integer with high order
bits taken from [z] and least significant bit [b]

- [shift_in_ind], [shift_in_pos_ind] induction schemes

- [shift_in_decomp] decompose an integer into its least significant
bit and the rest

- [testbit_decomp] decompose [Z.testbit] into a test on the least
significant bit or the rest

*)

Module Z.

  Definition shift_in (b : bool) (z : Z) : Z :=
    if b then Z.succ_double z else Z.double z.

  (** [shift_in] *)

  Lemma shift_in_spec b z : shift_in b z = 2 * z + (if b then 1 else 0).
  Proof.
    rewrite/shift_in. case: b=>/=.
    exact: Z.succ_double_spec. by rewrite Z.double_spec Z.add_0_r.
  Qed.

  #[global] Instance shift_in_inj : Inj2 (=) (=) (=) shift_in.
  Proof.
    move=>b1 z1 b2 z2. rewrite !shift_in_spec=>?.
    destruct b1, b2; simplify_eq/=; auto with lia.
  Qed.

  #[local] Lemma pos_xI_shift_in p : Z.pos p~1 = shift_in true (Z.pos p).
  Proof. by []. Qed.
  #[local] Lemma pos_xO_shift_in p : Z.pos p~0 = shift_in false (Z.pos p).
  Proof. by []. Qed.
  #[local] Lemma pos_1_shift_in : Z.pos 1 = shift_in true 0.
  Proof. by []. Qed.

  Lemma bits_shift_in b z i :
    0 ≤ i →
    Z.testbit (shift_in b z) i =
    if decide (i = 0) then b else Z.testbit z (Z.pred i).
  Proof.
    intros ?. rewrite shift_in_spec. case_decide.
    - subst i. by rewrite Z.testbit_0_r.
    - have ? : 0 ≤ Z.pred i by lia. set (j := Z.pred i) in *.
      have->: i = Z.succ j by rewrite/j Z.succ_pred.
      by rewrite Z.testbit_succ_r.
  Qed.

  Lemma testbit_shift_in_0 b z : Z.testbit (shift_in b z) 0 = b.
  Proof. by rewrite bits_shift_in. Qed.

  Lemma testbit_shift_in_succ b z i :
    0 ≤ i → Z.testbit (shift_in b z) (Z.succ i) = Z.testbit z i.
  Proof. intros. rewrite bits_shift_in ?decide_False; auto with f_equal. Qed.

  (** induction *)

  Lemma shift_in_ind (P : Z → Prop) :
    P 0 → (∀ b z, 0 ≤ z → P z → P (shift_in b z)) → ∀ z, 0 ≤ z → P z.
  Proof.
    intros ? Shift z ?. destruct z as [|p|]=>//. induction p.
    - rewrite pos_xI_shift_in. auto.
    - rewrite pos_xO_shift_in. auto.
    - rewrite pos_1_shift_in. exact: Shift.
  Qed.

  Lemma shift_in_pos_ind (P : Z → Prop) :
    P 1 → (∀ b z, 0 < z → P z → P (shift_in b z)) → ∀ z, 0 < z → P z.
  Proof.
    intros ? Shift ??. destruct z as [|p|]=>//. induction p.
    - rewrite pos_xI_shift_in. auto.
    - rewrite pos_xO_shift_in. auto.
    - done.
  Qed.

  (** decomposition *)

  Lemma shift_in_decomp z : z = shift_in (Z.odd z) (Z.div2 z).
  Proof. case: z => // -[] //= p. by rewrite Pos.pred_double_succ. Qed.

  Lemma testbit_decomp z i :
    0 ≤ i →
    Z.testbit z i =
    if decide (i = 0) then Z.odd z else Z.testbit (Z.div2 z) (Z.pred i).
  Proof. rewrite {1}(shift_in_decomp z). exact: bits_shift_in. Qed.

  (** [Z.succ] *)

  Lemma testbit_succ z i :
    0 ≤ i → Z.testbit z (Z.succ i) = Z.testbit (Z.div2 z) i.
  Proof. intros. rewrite testbit_decomp ?decide_False; auto with f_equal. Qed.

End Z.
