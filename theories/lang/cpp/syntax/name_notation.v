(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require bedrock.lang.cpp.syntax.core.
Require Export bedrock.lang.cpp.syntax.notations.
Require bedrock.lang.cpp.syntax.name_notation.parser.
Require bedrock.lang.cpp.syntax.name_notation.printer.

Bind Scope cpp_name_scope with core.name.

String Notation core.name parser.parse_name printer.print_name : cpp_name_scope.

(* Name Aliases *)
Bind Scope cpp_name_scope with core.globname.
Bind Scope cpp_name_scope with core.obj_name.
