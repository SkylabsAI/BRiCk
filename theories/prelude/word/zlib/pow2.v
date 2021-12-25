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
Require Import bedrock.prelude.word.zlib.base.

#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Powers of two *)

Module Z.

  Lemma pow2_pos n : 0 ≤ n → 0 < 2 ^ n.
  Proof. exact: Z.pow_pos_nonneg. Qed.
  #[global] Hint Resolve pow2_pos : core.

  Lemma pow2_succ n : 0 ≤ n → 2 ^ Z.succ n = 2 * 2 ^ n.
  Proof. intros. by rewrite Z.pow_succ_r. Qed.
  Lemma pow2_pred n : 0 < n → 2 * 2 ^ Z.pred n = 2 ^ n.
  Proof. intros. by rewrite Z_pow_pred_r. Qed.

  Lemma div2_pow2 n : 0 < n → Z.div2 (2 ^ n) = 2 ^ (n - 1).
  Proof.
    intros ?. rewrite Z.div2_div -pow2_pred//.
    by rewrite Z.mul_comm Z.div_mul.
  Qed.

  Lemma pow2_div2 n : 0 < n → 2 ^ n = 2 * Z.div2 (2 ^ n).
  Proof.
    intros ?. rewrite div2_pow2// -pow2_succ.
    by rewrite Z.succ_pred. lia.
  Qed.

  Lemma pow2_mod2 n : 0 < n → 2 ^ n `mod` 2 = 0.
  Proof.
    intros (k & -> & ?)%Z.lt_exists_pred.
    by rewrite pow2_succ// Z.mul_comm Z.mod_mul.
  Qed.

  Lemma pow2_strict n : 0 ≤ n → n < 2 ^ n.
  Proof. intros. exact: Z.pow_gt_lin_r. Qed.

  Lemma pow2_strict_2 n : 0 ≤ n → 2 * n - 1 < 2 ^ n.
  Proof.
    move/Z.natlike_cases=>[->|]; first done. intros (k & ? & ->).
    rewrite pow2_succ//. have := pow2_strict k ltac:(done). lia.
  Qed.

  Lemma pow2_bound z : ∃ n, 0 ≤ n ∧ z < 2 ^ n.
  Proof.
    case: (decide (0 ≤ z))=>Hz; last by exists 0; lia.
    pattern z. apply: natlike_ind z Hz; first by exists 0.
    move=>z Hz [n LT]. exists (Z.succ n). rewrite Z.pow_succ_r; lia.
  Qed.

  (** natural numbers *)

  Lemma pow2_S n : 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n.
  Proof. by rewrite Nat2Z.inj_succ pow2_succ. Qed.

End Z.
