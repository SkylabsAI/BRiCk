(*
 * Copyright (C) BedRock Systems Inc. 2021
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Export bedrock.prelude.word.zlib.base.
Require Export bedrock.prelude.word.zlib.pow2.
Require Export bedrock.prelude.word.zlib.mod_pow2.
Require Export bedrock.prelude.word.zlib.bit.
Require Export bedrock.prelude.word.zlib.twosc.
Require Export bedrock.prelude.word.zlib.eqmod.

Module Z.
  Export BinInt.Z.

  Export base.Z.	(** ./zlib/base.v *)
  Export pow2.Z.	(** ./zlib/pow2.v *)
  Export mod_pow2.Z.	(** ./zlib/mod_pow2.v *)
  Export bit.Z.		(** ./zlib/bit.v *)
  Export twosc.Z.	(** ./zlib/twosc.v *)
  Export eqmod.Z.	(** ./zlib/eqmod.v *)
End Z.
