(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.parser2.prelude.
Require Import bedrock.lang.cpp.parser2.lang.

(** * Derived types emitted by cpp2v *)

Module ParserType (Import Lang : PARSER_LANG).
  #[local] Notation globname := (globname parser_lang).
  #[local] Notation type := (type parser_lang).

  Definition Qconst_volatile : type -> type :=
    Tqualified QCV.
  Definition Qconst : type -> type :=
    Tqualified QC.
  Definition Qvolatile : type -> type :=
    Tqualified QV.
  Notation Qmut_volatile := Qvolatile (only parsing).
  Definition Qmut : type -> type :=
    Tqualified QM.

  (*
  Indicate that [underlying] is used to represent alias type [name].
  Enums are treated similarly.
  *)
  Definition Talias (name : globname) {underlying : type} : type :=
    underlying.
  Definition Tunderlying (enum : type) {underlying : type} : type :=
    underlying.
  Definition Tunary_xform (name : bs) (arg : type) {result : type} : type :=
    result.

  Notation Tdecay_type original adjusted := (adjusted) (only parsing).

End ParserType.
