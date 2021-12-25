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
Require Import bedrock.prelude.word.base.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Words 0, 1, -1 *)
(** Overview:

- [0], [1], [-1] for word types

*)
Module word.
  Import base.word.

  Definition zero (W : wordT) := of_Z W 0.
  Definition one (W : wordT) := of_Z W 1.
  Definition mone (W : wordT) := of_Z W (-1).

  #[global] Arguments zero : simpl never.
  #[global] Arguments one : simpl never.
  #[global] Arguments mone : simpl never.

  Module Import const_notation.
    Notation "0" := (zero _) : word_scope.
    Notation "1" := (one _) : word_scope.
    Notation "- 1" := (mone _) : word_scope.
    Notation "0 @{ W }" := (zero W) (only parsing) : word_scope.
    Notation "1 @{ W }" := (one W) (only parsing) : word_scope.
    Notation "( - 1 )@{ W }" := (mone W) (only parsing) : word_scope.
  End const_notation.

  Implicit Types W : wordT.

  Lemma to_Z_0 W : to_Z 0@{W} = 0.
  Proof. by rewrite to_of_Z_modulo. Qed.
  #[global] Hint Resolve to_Z_0 : core.

  Lemma signed_0 W : signed 0@{W} = 0.
  Proof.
    rewrite signed_of_Z//. have := half_modulus_min W. lia.
  Qed.
  #[global] Hint Resolve signed_0 : core.

  Lemma bits_0 W i : testbit 0@{W} i = false.
  Proof. by rewrite/testbit to_Z_0 Z.bits_0. Qed.
  #[global] Hint Resolve bits_0 : core.

  Lemma to_Z_1 W : to_Z 1@{W} = 1.
  Proof. rewrite to_of_Z//. have := modulus_min W. lia. Qed.
  #[global] Hint Resolve to_Z_1 : core.

  Lemma signed_1 W `{BitsizeAtLeast W 2} : signed 1@{W} = 1.
  Proof.
    rewrite signed_of_Z//. split; first by have := half_modulus_min W; lia.
    rewrite half_modulus_bitsize -{1}(Z.pow_0_r 2).
    generalize (bitsize_at_least W 2)=>?. apply Z.pow_lt_mono_r; lia.
  Qed.

  Lemma bits_1 W i : testbit 1@{W} i = bool_decide (i = 0).
  Proof. by rewrite/testbit to_Z_1 -Z.bits_1. Qed.

  Lemma m1_modulo W : (-1) `mod` modulus W = modulus W - 1.
  Proof.
    have->: (-1 = modulus W - 1 + -1 * modulus W)%Z by lia.
    rewrite Z.mod_add//. apply Z.mod_small. have := modulus_min W. lia.
  Qed.

  Lemma to_Z_m1 W : to_Z (-1)@{W} = modulus W - 1.
  Proof. by rewrite to_of_Z_modulo m1_modulo. Qed.

  Lemma signed_m1 W : signed (-1)@{W} = -1.
  Proof. rewrite signed_of_Z//. have := half_modulus_min W. lia. Qed.
  #[global] Hint Resolve signed_m1 : core.

  Lemma bits_m1 {W} i : 0 ≤ i < bitsize W → testbit (-1)@{W} i = true.
  Proof. destruct 1. by rewrite/mone testbit_of_Z// Z.bits_m1. Qed.

  #[local] Open Scope word_scope.

  Lemma one_nonzero W : 1 ≠ 0@{W}.
  Proof.
    enough (to_Z 1@{W} ≠ to_Z 0@{W}) by congruence.
    by rewrite to_Z_1 to_Z_0.
  Qed.
  #[global] Hint Resolve one_nonzero : core.

  Lemma m1_nonzero W : -1 ≠ 0@{W}.
  Proof.
    enough (signed (-1)@{W} ≠ signed 0@{W}) by congruence.
    by rewrite signed_m1 signed_0.
  Qed.
  #[global] Hint Resolve m1_nonzero : core.

  Lemma m1_ne_1 W `{BitsizeAtLeast W 2} : -1 ≠ 1@{W}.
  Proof.
    enough (signed (-1)@{W} ≠ signed 1@{W}) by congruence.
    by rewrite signed_m1 signed_1.
  Qed.
  #[global] Hint Resolve m1_ne_1 : core.

End word.
Export word.const_notation.
