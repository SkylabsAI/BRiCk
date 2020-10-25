(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Export bedrock.lang.prelude.base.

(** An exception monad. We offer no theory because this is currently
    used to compute things, not to prove things. *)
Variant exn {E A : Type} := Ret (x : A) | Exn (e : E).
Arguments exn _ _ : clear implicits, assert.

Instance exn_mret E : MRet (exn E) := λ A x, Ret x.
Instance exn_mbind E : MBind (exn E) := λ A B f m,
  match m with Ret x => f x | Exn e => Exn e end.
Instance exn_mjoin E : MJoin (exn E) := λ A m,
  match m with Ret m => m | Exn e => Exn e end.
Instance exn_fmap E : FMap (exn E) := λ A B f m,
  match m with Ret x => Ret (f x) | Exn e => Exn e end.
