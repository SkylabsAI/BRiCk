(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From stdpp Require Import countable strings.
Require Import bedrock.prelude.base.
Require Export bedrock.prelude.bytestring.

Set Primitive Projections.

#[local] Open Scope N_scope.

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
Definition globname : Set := ident.
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
Identify an aggregate field.
XXX: is this used for function members? If so, rename.
[Member] is taken, but [member_name] or shortenings of
[member_qualified_name] could work. *)
Record field : Set :=
{ f_type : globname (* name of containing aggregate *)
; f_name : ident
}.
#[global] Instance field_eq: EqDecision field.
Proof. solve_decision. Defined.

(**
[is_dependent x] means that [x : A] depends on template parameters.
*)
Class IsDependent A := is_dependent (x : A) : bool.
#[global] Hint Mode IsDependent + : typeclass_instances.
#[global] Arguments is_dependent : simpl never.

#[global] Instance option_is_dependent `{!names.IsDependent A} : IsDependent (option A) :=
  fun m =>
  if m is Some x then is_dependent x else false.

#[global] Instance list_is_dependent `{!names.IsDependent A} : IsDependent (list A) :=
  existsb is_dependent.

Section list.
  Context `{!names.IsDependent A}.
  Implicit Types (x : A) (xs : list A).

  Lemma is_dependent_True xs : is_dependent xs <-> Exists is_dependent xs.
  Proof. apply existb_True. Qed.
End list.

