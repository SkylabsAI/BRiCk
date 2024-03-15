(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.parser2.prelude.
Require Import bedrock.lang.cpp.parser2.lang.

#[local] Arguments force_some _ {_} : assert.	(** TODO: Upstream? *)

(** * Derived expressions emitted by cpp2v *)

Module ParserExpr (Import Lang : PARSER_LANG).
  #[local] Notation name := (name parser_lang).
  #[local] Notation obj_name := (obj_name parser_lang).
  #[local] Notation type := (type parser_lang).
  #[local] Notation exprtype := (exprtype parser_lang).
  #[local] Notation decltype := (decltype parser_lang).
  #[local] Notation Expr := (Expr parser_lang).

  Definition Eoperator_member_call (oo : OverloadableOperator) (nm : obj_name) (ct : dispatch_type) (ft : type) (obj : Expr) (es : list Expr) : Expr :=
    Eoperator_call oo (operator_impl.MFunc nm ct ft) (obj :: es).

  Definition Eoperator_call (oo : OverloadableOperator) (f : obj_name) (ft : type) (es : list Expr) : Expr :=
    Eoperator_call oo (operator_impl.Func f ft) es.

  Definition Eenum_const_at (gn : name) (c : ident) (ty : exprtype) : Expr :=
    Ecast Cintegral (Eenum_const gn c) Prvalue ty.

  Definition Ebuiltin (nm : obj_name) (ty : type) : Expr :=
    Ecast Cbuiltin2fun (Eglobal nm ty) Prvalue (Tptr ty).

  Definition Emember (arrow : bool) (e : Expr) (f : ident + name) (mut : bool) (ty : decltype) : force_some Expr :=
    option.get_some $
    let e :=
      if arrow then
        match drop_qualifiers $ type_of e with
        | Tptr t => Some (ast2.Ederef e t)
        | _ => None
        end
      else
        Some e
    in
    let k (e : Expr) : Expr :=
      match f with
      | inr on => Ecomma e (Eglobal on ty)
      | inl f => Emember e f mut ty
      end
    in
    k <$> e.

  Definition Edefault_init_expr (e : Expr) : Expr := e.

End ParserExpr.
