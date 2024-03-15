(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.parser2.prelude.
Require Import bedrock.lang.cpp.parser2.lang.
Import LangNotations.

(** * Derived declaration helpers emitted by cpp2v *)

Module ParserDecl (Import Lang : PARSER_LANG).
  #[local] Notation obj_name := (obj_name parser_lang).

  Definition pure_virt (on : obj_name) : obj_name * option obj_name :=
    (on, None).
  Definition impl_virt (on : obj_name) : obj_name * option obj_name :=
    (on, Some on).

End ParserDecl.
