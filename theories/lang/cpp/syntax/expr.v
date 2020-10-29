(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
From bedrock.lang.cpp.syntax Require Import names types.

Set Primitive Projections.

Definition Edefault_init_expr (e : Expr) : Expr := e.
