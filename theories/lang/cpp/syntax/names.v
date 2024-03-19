(*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.countable.
Require Import stdpp.strings.
Require Import bedrock.prelude.base.
Require Export bedrock.prelude.bytestring.

Set Primitive Projections.

#[local] Open Scope N_scope.

#[local] Notation EqDecision1 T := (∀ (A : Set), EqDecision A -> EqDecision (T A)) (only parsing).
#[local] Notation EqDecision2 T := (∀ (A : Set), EqDecision A -> EqDecision1 (T A)) (only parsing).
#[local] Tactic Notation "solve_decision" := intros; solve_decision.

(* this represents names that exist in object files. *)
Definition obj_name : Set := bs.
Bind Scope bs_scope with obj_name.
#[global] Instance obj_name_eq: EqDecision obj_name := _.

Definition ident : Set := bs.
Bind Scope bs_scope with ident.
#[global] Instance ident_eq: EqDecision ident := _.

(* naming in C++ is complex.
 * - everything has a path, e.g. namespaces, classes, etc.
 *   examples: ::foo         -- the namespace `foo`
 *             ::Foo         -- the class/struct/enum `Foo`
 *             ::Foo<int, 1> -- templated class (template parameters are types *and* expressions)
 * - functions (but not variables) can be overloaded.
 *   (this is addressed via name mangling)
 * - types (classes, structs, typedefs, etc) are not mangled because they are
 *   not present in the object file
 * - there are also "unnamed" functions, e.g. constructors and destructors
 *)
Definition globname : Set := bs.
Bind Scope bs_scope with globname.
  (* these are mangled names. for consistency, we're going to
   * mangle everything.
   *)
#[global] Instance globname_eq: EqDecision globname := _.

(* local names *)
Definition localname : Set := ident.
Bind Scope bs_scope with localname.
#[global] Instance localname_eq: EqDecision localname := _.

(**
NOTE: <<field_name>> analogous to <<atomic_name>>, and <<field>>
analogous to <<Nscoped>>.

We could likely switch to <<atomic_name>>, <<Nscoped>> with little
difficulty as the data carried by <<field_name.Anon>> serve only to
distguish distinct anonymous fields.
*)

Module field_name.
  Variant t {classname : Set} : Set :=
  | Id (_ : ident)
  | Anon (_ : classname).	(** anonymous field's type *)
  #[global] Arguments t : clear implicits.

  #[global] Instance t_eq_dec : EqDecision1 t.
  Proof. solve_decision. Defined.

  #[global] Instance t_countable {A : Set} `{!EqDecision A, !Countable A} :
    Countable (t A).
  Proof.
    apply (inj_countable'
      (fun n =>
      match n with
      | Id id => inl id
      | Anon cls => inr cls
      end)
      (fun n =>
      match n with
      | inl id => Id id
      | inr cls => Anon cls
      end)).
    abstract (by intros []).
  Defined.
End field_name.
Notation field_name := (field_name.t globname).

(**
Identify an aggregate field.
XXX: is this used for function members? If so, rename.
[Member] is taken, but [member_name] or shortenings of
[member_qualified_name] could work.
*)
Record field' {classname globname : Set} : Set := Build_field
{ f_type : globname (* name of containing aggregate *)
; f_name : field_name.t classname
}.
#[global] Arguments field' : clear implicits.
#[global] Arguments Build_field {_ _} _ _ : assert.
#[global] Instance field_eq : EqDecision2 field'.
Proof. solve_decision. Defined.
Notation field := (field' globname globname).
