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
 * Swasey had derived it from code original to the CompCert verified
 * compiler. That original code is
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

(** * [word n] *)
(** Overview:

- [word (n : nat) : Set] type of [n]-bit words

- [word_S (n : nat) : wordT] canonical proof of the word axioms for
[word (S n)]
*)

Record word {n : nat} : Set := Word {
  word_val : Z;
  (** Written this way for proof irrelevance. *)
  word_range : -1 < word_val < 2 ^ Z.of_nat n;
}.
Add Printing Constructor word.
#[global] Arguments word _ : clear implicits, assert.
#[global] Arguments Word {_ _} _ : assert.

Lemma Word_eq n {z1 z2} p1 p2 : z1 = z2 → @Word n z1 p1 = @Word n z2 p2.
Proof. intros ->. f_equal. apply proof_irrel. Qed.
(**
Arrange for [trivial] (and also [done]) to apply [Word_eq], stripping
off the proof-irrelevant bits so that tactics like [reflexivity] have
a chance to relate the integers. This matters in goals like [(-1)%i8 =
255%u8] where the words on the left and right hand sides carry the
same integer but different proofs.

The simpler [Hint Resolve Word_eq | 0 : core] would never fire because
[Word_eq] has a side-condition and [trivial] is non-recursive. [Hint
Immediate Word_eq : core] would never fire because such hints have
cost one and are skipped by [trivial].
*)
#[global] Hint Extern 0 (_ =@{word _}  _) =>
  apply Word_eq; solve [trivial] : core.

Section word.

  Lemma Word_pf n z : -1 < Z.mod_pow2 n z < 2 ^ Z.of_nat n.
  Proof. have := Z.mod_pow2_range n z. lia. Qed.

  #[local] Instance word_bitsize_nat n : word.BitsizeNat (word n) := n.
  #[local] Instance word_to_Z n : word.ToZ (word n) := word_val.
  #[local] Instance word_of_Z n : word.OfZ (word n) := fun z =>
    Word (Word_pf n z).

  #[local] Arguments word.bitsize_nat {_ _} / : assert.
  #[local] Arguments word_bitsize_nat _ / : assert.
  #[local] Arguments word.to_Z {_ _} _ / : assert.
  #[local] Arguments word.of_Z {_ _} _ / : assert.

  Lemma word_mixin {n} : n ≠ 0%nat → WordMixin (word n).
  Proof.
    split.
    - done.
    - move=>[x ?] /=. lia.
    - move=>z /=. apply Z.mod_pow2_spec.
    - move=>[x ?] /=. apply Word_eq.
      rewrite Z.mod_pow2_spec. apply Z.mod_small. lia.
  Qed.

  Lemma word_mixin_S n : WordMixin (word (S n)).
  Proof. exact: word_mixin. Qed.

  Canonical Structure word_S (n : nat) : wordT := WordT (word_mixin_S n).

  (** Note: Does not loop because the mode is [+ +]. *)
  #[global] Instance word_S_bitsize_at_least n n' :
    TCLeq (n' ?= S n)%nat → word.BitsizeAtLeast (word_S n) n'.
  Proof. by rewrite TCLeq_nat. Qed.

End word.
#[global] Hint Extern 0 (_ =@{word.word_car (word_S _)}  _) =>
  apply Word_eq; solve [trivial] : core.

Section examples.
  Goal word.signed $ word.of_Z (word 8) (-1) = -1.
  Proof. done. Abort.

  Goal word.to_Z $ word.of_Z (word 8) (-1) = 255.
  Proof. done. Abort.

  Goal word.modulus (word_S 7) = 256.
  Proof. done. Abort.
End examples.
