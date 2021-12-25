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
Require Import bedrock.prelude.word.zlib.pow2.

#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Fast normalization modulo [2 ^ n] *)
(** Overview:

- [Z.mod_pow2 (n : nat) (z : Z) : Z] computes [z `mod` 2 ^ n]

*)

Module Z.

  #[local] Definition P_mod_pow2 : nat -> positive -> Z :=
    fix go n p {struct n} :=
    match n with
    | O => 0
    | S n =>
      match p with
      | xH => 1
      | xO p => Z.double (go n p)
      | xI p => Z.succ_double (go n p)
      end
    end.

  Definition mod_pow2 (n : nat) (z : Z) : Z :=
    match z with
    | Z0 => 0
    | Zpos p => P_mod_pow2 n p
    | Zneg p =>
      let r := P_mod_pow2 n p in
      if decide (r = 0) then 0 else two_power_nat n - r
    end.

  #[local] Lemma P_mod_pow2_range n p : 0 ≤ P_mod_pow2 n p < 2 ^ Z.of_nat n.
  Proof.
    revert p. induction n as [|n IH]; simpl; intros; first done.
    rewrite Z.pow2_S. destruct p as [p|p|].
    - rewrite Z.succ_double_spec. specialize (IH p). lia.
    - rewrite Z.double_spec. specialize (IH p). lia.
    - clear IH. generalize (Z.pow2_pos $ Z.of_nat n). lia.
  Qed.

  #[local] Lemma P_mod_pow2_spec n p :
    P_mod_pow2 n p = Z.pos p `mod` 2 ^ Z.of_nat n.
  Proof.
    suff [y Hy] : ∃ y, Zpos p = 2 ^ Z.of_nat n * y + P_mod_pow2 n p.
    { apply: Z.mod_unique_pos Hy. apply P_mod_pow2_range. }
    revert p. induction n as [|n IH]=>p /=.
    { by exists (Zpos p). }
    rewrite Z.pow2_S. destruct p as [p|p|].
    - destruct (IH p) as [y EQ]. exists y. lia.
    - destruct (IH p) as [y EQ]. exists y. lia.
    - exists 0. lia.
  Qed.

  Lemma mod_pow2_spec n z : mod_pow2 n z = z `mod` 2 ^ Z.of_nat n.
  Proof.
    rewrite/mod_pow2. destruct z as [|p|p].
    { by rewrite Zmod_0_l. }
    { apply P_mod_pow2_spec. }
    have ? := P_mod_pow2_range n p. have Hn : 2 ^ Z.of_nat n ≠ 0 by lia.
    have {Hn}:= Z.div_mod (Zpos p) _ Hn. rewrite -P_mod_pow2_spec.
    rewrite -Pos2Z.opp_pos two_power_nat_equiv=>->.
    set q := _ `div` _. set r := P_mod_pow2 _ _. case_decide as EQr.
    - apply Z.mod_unique_pos with (-q); rewrite ?EQr; lia.
    - apply Z.mod_unique_pos with (-q - 1); lia.
  Qed.

  Lemma mod_pow2_range n z : 0 ≤ mod_pow2 n z < 2 ^ Z.of_nat n.
  Proof. rewrite mod_pow2_spec. auto using Z.mod_pos_bound. Qed.

End Z.
