(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require bedrock.lang.cpp.syntax.core.
Require bedrock.lang.cpp.syntax.name_notation.parser.
Require bedrock.lang.cpp.syntax.name_notation.printer.

Declare Scope cpp_name_scope.
Delimit Scope cpp_name_scope with cpp_name.
Bind Scope cpp_name_scope with core.name.
String Notation core.name parser.parse_name printer.print_name : cpp_name_scope.

(*
Definition test : name :=
  Nscoped (Nglobal (Nid "XX")) (Nfunction [] (Nf "foo") [Tint;Tchar;Tlong;Tlonglong;Tulonglong;Tptr Tvoid]).


Require Import bedrock.lang.cpp.syntax.pretty.

Definition parse_name (test : list Byte.byte) : option name :=
  parser.run_full (parser.parse_name 1000) $ BS.parse test.

Declare Scope cpp_name_scope.
Delimit Scope cpp_name_scope with cpp_name.

Search bs list Byte.byte.
Definition print_raw : name -> option (list Byte.byte) := fun _ => Some (BS.print """hello world""").
Definition parse_raw : list Byte.byte -> option name := fun _ => None.


Definition dont_print : name -> option (list Byte.byte) := fun _ => None.
Definition dont_parse : list Byte.byte -> option name := fun _ => None.


(*
String Notation name dont_parse dont_print : cpp_name_scope.
String Notation name parse_raw print_raw : cpp_name_scope.
*)


Module X.
#[local] String Notation name parse_name print_name : cpp_name_scope.

Definition test : name :=
  Nscoped (Nglobal (Nid "XX")) (Nfunction [] (Nf "foo") [Tint;Tchar;Tlong;Tlonglong;Tulonglong;Tptr Tvoid]).
Print test.
Definition test2 : name :=
  "XX<int,$T>::operator--(const int, char*, long, long long, unsigned long long, void* )"%cpp_name.
Print test2.
End X.

Notation Nscoped a := (Nscoped a).


Close Scope cpp_name_scope.
Print X.test2.
*)
