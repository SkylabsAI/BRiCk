(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.prelude.word.base.
Require Import bedrock.prelude.word.aux_arg.

(** * Number notation support for word types *)
(** Overview:

The details here don't matter much unless you want to add number
notation for additional word types. In that case, see the
documentation of Coq's [Number Notation] command and ./aux.v for
examples.

Note: Bounds checks matter. We could set up notation in scope [%W]
inferring an arbitrary word type [W : wordT] from context and just
hitting the number with [word.of_Z]. Such notation would be
misleading, due to truncation; for example, [0x100%W : word 8] would
print as 255 but denote zero.

*)

Module Type WORD_NUM (Import WT : WORD_TYPE).

  Import base.word.

  (** Representation function, as well as a spec for zify (see ./aux.v). *)

  Definition of_Z : Z → word_car W := of_Z W.
  Lemma of_Z_spec : of_Z = word.of_Z W.
  Proof. done. Qed.

  (** Inductive wrapper *)

  Variant num : Set := Num (z : Z).

  (** Parse unsigned or signed *)

  Definition uparse (z : Z) : option num :=
    guard (is_unsigned W z); Some (Num z).
  Definition sparse (z : Z) : option num :=
    guard (is_signed W z); Some (Num z).

  (** Print decimal or hexadecimal *)

  Definition dprint '(Num z) : Z := z.
  Definition xprint '(Num z) : Number.int :=
    Number.IntHexadecimal $ Z.to_hex_int z.

End WORD_NUM.
