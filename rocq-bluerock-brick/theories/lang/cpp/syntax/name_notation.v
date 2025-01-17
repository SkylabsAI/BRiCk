(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require bedrock.lang.cpp.syntax.core.
Require Export bedrock.lang.cpp.syntax.notations.
Require bedrock.lang.cpp.syntax.name_notation.parser.
Require bedrock.lang.cpp.syntax.name_notation.printer.

Bind Scope cpp_name_scope with core.name.

(** Un-checked scopes allow locally opting out of name checking *)
Declare Scope cpp_name_unchecked_scope.
Delimit Scope cpp_name_unchecked_scope with cpp_name_unchecked.
Declare Scope cpp_type_unchecked_scope.
Delimit Scope cpp_type_unchecked_scope with cpp_type_unchecked.
Declare Scope cpp_field_unchecked_scope.
Delimit Scope cpp_field_unchecked_scope with cpp_field_unchecked.

#[local]
Definition parse_name (s : PrimString.string) := parser.parse_name s.
#[local]
Definition print_name (bs : core.name) := printer.print_name bs.
String Notation core.name parse_name print_name : cpp_name_scope.
String Notation core.name parse_name print_name : cpp_name_unchecked_scope.

(* Name Aliases *)
Bind Scope cpp_name_scope with core.globname.
Bind Scope cpp_name_scope with core.obj_name.

(* the parser for fields adds a sanity check that it starts with [Nscoped] *)
#[local]
Definition parse_field_with check (ls : PrimString.string) : option core.field :=
  match parser.parse_name_with check ls with
  | Some (core.Nscoped _ _) as x => x
  | _ => None
  end.

#[local]
Definition parse_field (ls : PrimString.string) : option core.field :=
  match parse_name ls with
  | Some (core.Nscoped _ _) as x => x
  | _ => None
  end.
#[local]
Definition print_field (f : core.field) : option PrimString.string :=
  match f with
  | core.Nscoped _ _ => print_name f
  | _ => None
  end.
String Notation core.field parse_field print_field : cpp_field_scope.
String Notation core.field parse_field print_field : cpp_field_unchecked_scope.


Fail Check "foo"%cpp_field.
Succeed Example _0 : "foo"%cpp_name = "foo"%cpp_name := eq_refl.

(** String Notations for types *)
#[local]
Definition parse_type (s : PrimString.string) := parser.parse_type s.
#[local]
Definition print_type (bs : core.type) := printer.print_type bs.
String Notation core.type parse_type print_type : cpp_type_scope.
String Notation core.type parse_type print_type : cpp_type_unchecked_scope.
Bind Scope cpp_type_scope with core.type.
