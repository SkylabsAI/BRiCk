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
Require Import bedrock.prelude.word.zlib.bit.

#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Twos complement numbers *)
(** Some facts relevant to [n]-bit twos-complement numbers:

- [bits_above] unsigned twos-complement numbers have no bits above
[n] set

- [bits_above_neg] negative twos-complement numbers have all bits
above [n] set

- [sign_bit] the most significant bit is set iff its twos-complement
representation is [≥ 2^(n-1)]

*)

Module Z.

  Lemma bits_above n z i :
    0 ≤ n → 0 ≤ z < 2 ^ n → n ≤ i → Z.testbit z i = false.
  Proof.
    move=>Hn. revert z i. pattern n.
    apply: natlike_ind n Hn=> [|n ? IH] z i Hz Hi.
    { rewrite Z.pow_0_r in Hz. have->: z = 0 by lia. apply Z.testbit_0_l. }
    rewrite Z.testbit_decomp ?decide_False ?IH; auto with lia.
    rewrite Z.pow2_succ// (Z.shift_in_decomp z) Z.shift_in_spec in Hz.
    destruct (Z.odd z); lia.
  Qed.

  Lemma ones_complement i z : 0 ≤ i → Z.testbit (-z-1) i = negb (Z.testbit z i).
  Proof.
    move=>Hi. move: i Hi z=>i Hi. pattern i. apply: Zlt_0_ind Hi=>{}i IH Hi z.
    rewrite (Z.shift_in_decomp z). set z' := Z.div2 z.
    have->: - Z.shift_in (Z.odd z) z' - 1 = Z.shift_in (negb (Z.odd z)) (- z' - 1).
    { rewrite !Z.shift_in_spec. destruct (Z.odd z); simpl; lia. }
    rewrite !Z.bits_shift_in //. case_decide; auto with lia.
  Qed.

  Lemma bits_above_neg n z i :
    0 ≤ n → - 2 ^ n ≤ z < 0 → n ≤ i → Z.testbit z i = true.
  Proof.
    intros ? Hz Hi. set z' := (-z-1).
    have {Hz} : Z.testbit z' i = false by apply: bits_above Hi; lia.
    rewrite /z' ones_complement ?negb_false_iff; auto with lia.
  Qed.

  Lemma sign_bit n z :
    0 ≤ n → 0 ≤ z < 2 ^ Z.succ n →
    Z.testbit z n = negb (bool_decide (z < 2 ^ n)).
  Proof.
    move=>Hn. revert z. pattern n. apply: natlike_ind n Hn=> [|n ? IH] z Hz.
    { rewrite Z.pow_1_r in Hz. have {}Hz: z = 0 ∨ z = 1 by lia.
      by destruct Hz; subst z. }
    rewrite Z.testbit_decomp ?decide_False; auto. rewrite Z.pred_succ {}IH.
    - f_equal. rewrite Z.pow_succ_r// [z in RHS]Z.shift_in_decomp Z.shift_in_spec.
      case_bool_decide.
      + rewrite bool_decide_true//. destruct (Z.odd z); simpl; lia.
      + rewrite bool_decide_false//. destruct (Z.odd z); simpl; lia.
    - rewrite (Z.shift_in_decomp z) Z.shift_in_spec Z.pow2_succ in Hz; last lia.
      destruct (Z.odd z); lia.
  Qed.

End Z.
