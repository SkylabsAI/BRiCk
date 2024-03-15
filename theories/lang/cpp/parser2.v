(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bedrock.prelude.base.	(* for, e.g., <<::>> *)
Require Export bedrock.prelude.bytestring.	(* for <<%bs>> *)
Require Import bedrock.prelude.avl.
Require Export bedrock.lang.cpp.syntax2.syntax1.
Require Export bedrock.lang.cpp.syntax2.ast2.
Require Export bedrock.lang.cpp.parser2.parser1.
Require Import bedrock.lang.cpp.parser2.lang.
Require Import bedrock.lang.cpp.parser2.type.
Require Import bedrock.lang.cpp.parser2.expr.
Require Import bedrock.lang.cpp.parser2.decl.

#[local] Definition parser_lang : Set := cpp.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Module Import translation_unit.

  (**
  We work with an exploded [translation_unit] and raw trees for
  efficiency.
  *)

  Definition raw_symbol_table : Type := IM.Raw.tree SObjValue.
  Definition raw_type_table : Type := IM.Raw.tree SGlobDecl.
  Definition raw_alias_table : Type := IM.Raw.tree Stype.

  Definition t : Type :=
    raw_symbol_table -> raw_type_table -> raw_alias_table ->
    (raw_symbol_table -> raw_type_table -> raw_alias_table -> translation_unit) ->
    translation_unit.

  Definition _symbols (f : raw_symbol_table -> raw_symbol_table) : t :=
    fun s t a k => k (f s) t a.
  Definition _types (f : raw_type_table -> raw_type_table) : t :=
    fun s t a k => k s (f t) a.
  Definition _aliases (f : raw_alias_table -> raw_alias_table) : t :=
    fun s t a k => k s t (f a).
  Definition _skip : t :=
    fun s t a k => k s t a.

  Fixpoint decls' (ds : list t) : t :=
    match ds with
    | nil => fun s t a k => k s t a
    | d :: ds => fun s t a k => d s t a (fun s t a => decls' ds s t a k)
    end.

  Definition decls (ds : list t) (e : endian) : translation_unit :=
    decls' ds ∅ ∅ ∅ $ fun s t a => {|
      symbols := avl.from_raw s;
      types := avl.from_raw t;
      aliases := avl.from_raw a;
      initializer := nil;	(** TODO *)
      byte_order := e;
    |}.

End translation_unit.
Export translation_unit(decls).
#[local] Notation K := translation_unit.t (only parsing).
#[local] Notation globname := names.globname.
#[local] Notation obj_name := names.obj_name.

Definition Dvariable (n : obj_name) (t : Stype) (init : option SExpr) : K :=
  _symbols <[n := Ovar t init]>.

Definition Dfunction (n : obj_name) (f : SFunc) : K :=
  _symbols <[n := Ofunction f]>.

Definition Dmethod (n : obj_name) (static : bool) (f : SMethod) : K :=
  _symbols <[n := if static then Ofunction $ static_method f else Omethod f]>.

Definition Dconstructor (n : obj_name) (f : SCtor) : K :=
  _symbols <[n := Oconstructor f]>.

Definition Ddestructor (n : obj_name) (f : SDtor) : K :=
  _symbols <[n := Odestructor f]>.

Definition Dtype (n : globname) : K :=
  _types <[n := Gtype]>.

Definition Dstruct (n : globname) (f : option SStruct) : K :=
  _types <[n := if f is Some f then Gstruct f else Gtype]>.

Definition Dunion (n : globname) (f : option SUnion) : K :=
  _types <[n := if f is Some f then Gunion f else Gtype]>.

Definition Denum (n : globname) (u : Stype) (cs : list ident) : K :=
  _types <[n := Genum u cs]>.

Definition Denum_constant (n : globname)
    (gn : Sglobname) (ut : Sexprtype) (v : N + Z) (init : option SExpr) : K :=
  _types $ insert n $
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  Gconstant t $ Some $ Ecast Cintegral v Prvalue t.

Definition Dtypedef (n : globname) (t : Stype) : K :=
  _aliases <[n := t]>.

Definition Dstatic_assert (msg : option bs) (e : SExpr) : K :=
  _skip.

(*
Declare Reduction reduce_translation_unit := vm_compute.	(* in ./parser.v *)
*)
