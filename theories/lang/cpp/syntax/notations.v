(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.parser.notation.

Declare Scope cpp_scope.
Delimit Scope cpp_scope with cpp.

Declare Scope cppfield_scope.
Delimit Scope cppfield_scope with field.

Declare Scope cppname_scope.
Delimit Scope cppname_scope with cppname.

(* XXX This is only parsing to work around Coq misusing it outside
[cppfield_scope]. See #235. *)
Notation "` e `" := e (e custom cppglobal at level 200, at level 0,
                        only parsing) : cppfield_scope.
Notation "` e `" := e (e custom cppglobal at level 200, at level 0,
                        only parsing) : cppname_scope.


(** Importing [cpp_notation] makes cpp2v-generated names generally
available as, e.g., [``::MyClass``]. *)
Module Export cpp_notation.
  Notation "'``' e '``'" := e
                              (at level 0, e custom cppglobal at level 200,
                                format "`` e ``") : cpp_scope.
  Open Scope cpp_scope.
End cpp_notation.
