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

#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** Simple facts about [Z] *)

Module Z.

  #[global] Arguments Z.div2 : simpl never.
  #[global] Hint Resolve Nat2Z.is_nonneg : core.
  #[global] Hint Resolve Z.pred_succ : core.

  Lemma natlike_cases n : 0 ≤ n → n = 0 ∨ ∃ k, 0 ≤ k ∧ n = Z.succ k.
  Proof.
    intros. destruct (decide (n = 0)) as [->|?]; [by left|right].
    exists (Z.pred n). lia.
  Qed.

  (** [Z.succ] *)

  Lemma succ_nonneg_nonzero n : 0 ≤ n → Z.succ n ≠ 0.
  Proof. lia. Qed.
  #[global] Hint Resolve succ_nonneg_nonzero : core.

  Lemma succ_nonneg_nonneg n : 0 ≤ n → 0 ≤ Z.succ n.
  Proof. lia. Qed.
  #[global] Hint Resolve succ_nonneg_nonneg : core.

  (** [Z.testbit] *)

  Lemma bits_1 i : Z.testbit 1 i = bool_decide (i = 0).
  Proof. by destruct i. Qed.

  Lemma testbit_nonneg x y i :
    (0 ≤ i → Z.testbit x i = Z.testbit y i) → Z.testbit x i = Z.testbit y i.
  Proof.
    intros H. destruct (Z.neg_nonneg_cases i).
    by rewrite !Z.testbit_neg_r. exact: H.
  Qed.

  (**
  Easy corollary of [Z.bits_inj_iff], making [0 ≤ i] available in the
  premiss.
  *)
  Lemma bits_eq x y : (∀ i, 0 ≤ i → Z.testbit x i = Z.testbit y i) → x = y.
  Proof. intros. apply Z.bits_inj_iff=>i. auto using testbit_nonneg. Qed.

  (** natural numbers *)

  Lemma of_nat_pos n : n ≠ 0%nat → 0 < Z.of_nat n.
  Proof. lia. Qed.
  #[global] Hint Resolve of_nat_pos : core.

End Z.
