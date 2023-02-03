(*
 * Copyright (c) 2020-22 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** ** Primitive Conversions

    This file covers conversions between primitive types.
 *)
From bedrock.prelude Require Import base numbers.
From bedrock.lang.cpp.arith Require Export operator.
From bedrock.lang.cpp Require Import ast semantics.values semantics.promotion.

#[local] Open Scope Z_scope.
