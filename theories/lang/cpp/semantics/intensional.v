(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
(* This file contains intensional functions necessary to
 * describe the semantics of our AST.
 *
 * It would be great if we could eliminate this, but it
 * requires some more thought.
 *
 * Another option would be to completely pre-process the
 * AST and remove these nodes.
 *)
Require Import Coq.ZArith.ZArith_base.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.values.

(* if an expression is being constructed into an object not owned by
 * the lexical scope of this object, then we won't be in charge of
 * running the destructor
 *)
Fixpoint not_mine (e : Expr) : Expr :=
  match e with
  | Ebind_temp e _ => e
  | Eandclean e _ => not_mine e
  | _ => e
  end.

(* this function determines whether the type is an aggregate type, i.e.
 * arrays and objects.
 *)
Fixpoint is_aggregate (t : type) : bool :=
  match t with
  | Tnamed _
  | Tarray _ _ => true
  | Tqualified _ t => is_aggregate t
  | _ => false
  end.

Fixpoint is_void (t : type) : bool :=
  match t with
  | Tqualified _ t => is_void t
  | Tvoid => true
  | _ => false
  end.

(* the default value for a type.
 * this is used to initialize primitives if you do, e.g.
 *   [int x{};]
 *)
Fixpoint get_default (t : type) : option val :=
  match t with
  | Tpointer _ => Some (Vptr nullptr)
  | Tint _ _ => Some (Vint 0%Z)
  | Tbool => Some (Vbool false)
  | Tnullptr => Some (Vptr nullptr)
  | Tqualified _ t => get_default t
  | _ => None
  end.

(* this determines whether a type is initializable from a primitive.
 *)
Fixpoint prim_initializable (t : type) : bool :=
  match t with
  | Tpointer _
  | Tint _ _
  | Tbool
  | Tnullptr => true
  | Tqualified _ t => prim_initializable t
  | _ => false
  end.
