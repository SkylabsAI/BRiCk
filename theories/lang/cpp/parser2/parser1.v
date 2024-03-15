(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.parser2.prelude.

Require bedrock.lang.cpp.syntax.expr.
Export expr.new_form(
  Allocating,
  NonAllocating
).

Require Export bedrock.lang.cpp.parser(
  (** relevant to keys in translation units *)
  DTOR,

  (** generic *)
  Sforeach,
  Sreturn_val,
  Sreturn_void

  (**
  TODO:
  Dstatic_assert
  Tdecay_type
  Tvariable_array
  mk_overrides
  mk_virtuals
  *)
).
