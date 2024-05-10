(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export bedrock.prelude.base.	(* for, e.g., <<::>> *)
Require Export bedrock.prelude.bytestring.	(* for <<%bs>> *)
Require Import bedrock.prelude.avl.
Require Export bedrock.lang.cpp.syntax. (* NOTE: too much *)
Require Export bedrock.lang.cpp.parser.stmt.
Require Import bedrock.lang.cpp.parser.lang.
Require Import bedrock.lang.cpp.parser.type.
Require Import bedrock.lang.cpp.parser.expr.
Require Import bedrock.lang.cpp.parser.decl.
Require Import bedrock.lang.cpp.parser.notation.
Require Import bedrock.lang.cpp.parser.reduction.

#[local] Definition parser_lang : lang.t := lang.cpp.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Module Import translation_unit.

  (**
  We work with an exploded [translation_unit] and raw trees for
  efficiency.
  *)

  Definition raw_symbol_table : Type := NM.Raw.t ObjValue.
  Definition raw_type_table : Type := NM.Raw.t GlobDecl.
  Definition raw_alias_table : Type := NM.Raw.t type.

  #[global] Instance raw_structured_insert : forall {T}, Insert globname T (NM.Raw.t T) := _.

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
      symbols := NM.from_raw s;
      types := NM.from_raw t;
      aliases := NM.from_raw a;
      initializer := nil;	(** TODO *)
      byte_order := e;
    |}.

End translation_unit.
Export translation_unit(decls).
#[local] Notation K := translation_unit.t (only parsing).

Definition Dvariable (n : obj_name) (t : type) (init : option Expr) : K :=
  _symbols <[n := Ovar t init]>.

Definition Dfunction (n : obj_name) (f : Func) : K :=
  _symbols <[n := Ofunction f]>.

Definition Dmethod (n : obj_name) (static : bool) (f : Method) : K :=
  _symbols <[n := if static then Ofunction $ static_method f else Omethod f]>.

Definition Dconstructor (n : obj_name) (f : Ctor) : K :=
  _symbols <[n := Oconstructor f]>.

Definition Ddestructor (n : obj_name) (f : Dtor) : K :=
  _symbols <[n := Odestructor f]>.

Definition Dtype (n : globname) : K :=
  _types <[n := Gtype]>.

Definition Dstruct (n : globname) (f : option Struct) : K :=
  _types <[n := if f is Some f then Gstruct f else Gtype]>.

Definition Dunion (n : globname) (f : option Union) : K :=
  _types <[n := if f is Some f then Gunion f else Gtype]>.

Definition Denum (n : globname) (u : type) (cs : list ident) : K :=
  _types <[n := Genum u cs]>.

Definition Denum_constant (n : globname)
    (gn : globname) (ut : exprtype) (v : N + Z) (init : option Expr) : K :=
  _types $ insert n $
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  Gconstant t $ Some $ Ecast (Cintegral t) v.

Definition Dtypedef (n : globname) (t : type) : K :=
  _aliases <[n := t]>.

Definition Dstatic_assert (msg : option bs) (e : Expr) : K :=
  _skip.
