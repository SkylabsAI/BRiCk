(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Export bedrock.prelude.word.base.
Require Export bedrock.prelude.word.finite.
Require Export bedrock.prelude.word.type.
Require Export bedrock.prelude.word.const.
Require Export bedrock.prelude.word.add.
Require bedrock.prelude.word.aux.

Module word.
  Export base.word.	(** ./word/base.v *)
  Export finite.word.	(** ./word/finite.v *)
  Export const.word.	(** ./word/const.v *)
  Export add.word.	(** ./word/add.v *)
End word.
Export aux.notation.
