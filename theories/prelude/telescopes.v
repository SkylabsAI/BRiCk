(*
 * Copyright (c) 2020-2021 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Export stdpp.telescopes.
Require Import bedrock.prelude.base.

#[local] Set Universe Polymorphism.

Fixpoint tele_append (t : tele) {struct t}: (t -t> tele) -> tele :=
  match t as t return (t -t> tele) -> tele with
  | TeleO => fun x : tele => x
  | @TeleS T f => fun x => @TeleS T (fun t => tele_append (f t) (x t))
  end.

Definition tele_fun_pointwise@{X Z Y} {t : tele@{X}} {A : Type@{Z}}
    (R : A -> A -> Prop) (f g : tele_fun@{X Z Y} t A) : Prop :=
  forall x, R (tele_app f x) (tele_app g x).

(** Fix inference for upstream definitions. *)
Polymorphic Definition TargO : tele_arg TeleO := tt.
Polymorphic Definition TargS {T} {TT : T -> tele} (a : T) (b : tele_arg (TT a)) : tele_arg (TeleS TT) :=
  @TeleArgCons _ (λ x, tele_arg _) a b.

(** Shadow iris notations using [TargO] and [Targ] *)
Notation "'[tele_arg' x ; .. ; z ]" :=
  (TargS x ( .. (TargS z TargO) ..))
  (format "[tele_arg  '[hv' x ;  .. ;  z ']' ]").
Notation "'[tele_arg' ]" := (TargO)
  (format "[tele_arg ]").
