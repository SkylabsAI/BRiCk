(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Export stdpp.telescopes.
Require Import bedrock.lang.prelude.base.

Set Universe Polymorphism.
Unset Auto Template Polymorphism.

Reserved Notation "! x" (at level 35, right associativity, format "! x").

Declare Scope tele_scope.
Delimit Scope tele_scope with tele.
Bind Scope tele_scope with tele.

Infix "<$>" := tele_map : tele_scope.	(** [fmap] isn't universe polymorphic *)

Declare Scope tele_fun_scope.
Delimit Scope tele_fun_scope with tele_fun.
Bind Scope tele_fun_scope with tele_fun.

Definition tele_const {T} (v : T) : ∀ {t : tele}, t -t> T :=
  fix go t :=
  match t with
  | TeleO => v
  | TeleS bnd => fun x => go (bnd x)
  end.
Global Arguments tele_const {_} _ {!_} : assert.
Notation "! v" := (tele_const v) : tele_fun_scope.

Lemma tele_const_app {T} (v : T) {t : tele} (args : t) :
  tele_app (tele_const v) args = v.
Proof. by induction args. Qed.

Fixpoint tele_append (t : tele) {struct t}: (t -t> tele) -> tele :=
  match t as t return (t -t> tele) -> tele with
  | TeleO => fun x : tele => x
  | @TeleS T f => fun x => @TeleS T (fun t => tele_append (f t) (x t))
  end.
Infix "++" := tele_append : tele_scope.

(** Add binders to telescopic functions in sigma-like types. *)
Definition tele_fun_append {Sig A} {_tele : Sig -> tele}
    (_fun : ∀ (sig : Sig), _tele sig -t> A) :
    ∀ (t : tele) (f : t -t> Sig), (t ++ (_tele <$> f))%tele -t> A :=
  fix go t :=
  match t with
  | TeleO => _fun
  | TeleS bnd => fun f x => go _ (f x)
  end.
Global Arguments tele_fun_append _ _ _ _ & !_ _ / : assert.

(** A variant of [tele_fun_append] for type families indexed by
    telescopes. This is weaker because telescope [t2] does not depend
    on telescope [t1]. *)
Definition tele_fun_append_weak {T : tele -> Type} {A}
    (_fun : ∀ {t2}, T t2 -> t2 -t> A) :
    ∀ (t1 : tele) {t2 : tele} (f : t1 -t> T t2), (t1 ++ !t2)%tele -t> A :=
  fix go t1 {t2} :=
  match t1 with
  | TeleO => _fun
  | TeleS bnd => fun f x => go _ (f x)
  end.
Global Arguments tele_fun_append_weak _ _ _ & !_ _ _ : assert.

Definition tele_map_2 {T U} (f : T -> U) {t1 t2} :
    (t1 -t> t2 -t> T) -> t1 -t> t2 -t> U :=
  tele_map (tele_map f).
Global Arguments tele_map_2 _ _ _ !_ _ _ / : assert.

Definition tele_app_2 {t1 t2 T} (f : t1 -t> t2 -t> T) : t1 -> t2 -> T :=
  tele_app (tele_map tele_app f).
Global Arguments tele_app_2 !_ _ _ _ / _ _ : assert.
