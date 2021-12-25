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

Require Import stdpp.finite.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.word.base.

(** * Word types are finite *)

Module word.
  Import base.word.

  Section finite.

    Context {W : wordT}.

    (** Not an instance to avoid accidentally computing [enum W]. *)
    Program Definition word_finite : Finite W :=
      enc_finite (Z.to_nat ∘ to_Z) (of_Z W ∘ Z.of_nat)
        (Z.to_nat (modulus W)) _ _ _.
    Next Obligation. move=>x /=. by rewrite Z2Nat.id. Qed.
    Next Obligation. move=>x /=. by rewrite -Z2Nat.inj_lt. Qed.
    Next Obligation.
      move=>n /=. rewrite Nat2Z.inj_lt Z2Nat.id// =>?.
      by rewrite to_of_Z ?Nat2Z.id.
    Qed.

  End finite.

End word.
