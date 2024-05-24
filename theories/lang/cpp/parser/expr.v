(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax.types(drop_qualifiers).
Require Import bedrock.lang.cpp.parser.prelude.
Require Import bedrock.lang.cpp.parser.lang.

#[local] Arguments force_some _ {_} : assert.	(** TODO: Upstream? *)

(** * Derived expressions emitted by cpp2v *)

Module ParserExpr (Import Lang : PARSER_LANG).
  #[local] Notation name := (name' parser_lang).
  #[local] Notation obj_name := (obj_name' parser_lang).
  #[local] Notation type := (type' parser_lang).
  #[local] Notation exprtype := (exprtype' parser_lang).
  #[local] Notation decltype := (decltype' parser_lang).
  #[local] Notation Expr := (Expr' parser_lang).
  #[local] Notation Cast := (Cast_ type type).

  Definition Ecstyle_cast (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast cast_style.c t (Ecast c e).
  Definition Efunctional_cast (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast cast_style.functional t (Ecast c e).

  Definition fuse_dependent_cast (s : cast_style.t) (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast s t (Ecast c e).
(*
    match c with
    | Cdependent t' =>
        if bool_decide (t = t') then
          Eexplicit_cast s t e
        else
          Eexplicit_cast s t (Ecast c e)
    (* TODO: use [Eunsupported] *)
    | _ =>
        Eexplicit_cast s t (Ecast c e)
    end.
*)

  (* Keeping [Eexplicit_cast] as an annotation (with a no-op semantics) makes it easy
     to give it semantics.
     Alternatively, we could fuse these symbols, but then we would need to give
     separate rules for each type of cast at each WP.
   *)
  Definition Edynamic_cast (c : Cast) (t : type) (e : Expr) : Expr :=
    Eexplicit_cast cast_style.dynamic t (Ecast c e).

    (*
    match c with
    | Cdynamic t' =>
        if bool_decide (t = t') then
          Eexplicit_cast cast_style.dynamic t e
        else
          Eexplicit_cast cast_style.dynamic t (Ecast c e)
    | _ =>
        fuse_dependent_cast cast_style.dynamic c t e
    end. *)
  Definition Estatic_cast := fuse_dependent_cast cast_style.static.
  Definition Econst_cast := fuse_dependent_cast cast_style.const.
  Definition Ereinterpret_cast := fuse_dependent_cast cast_style.reinterpret.

  Definition Eoperator_member_call (oo : OverloadableOperator) (nm : obj_name) (ct : dispatch_type) (ft : type) (obj : Expr) (es : list Expr) : Expr :=
    Eoperator_call oo (operator_impl.MFunc nm ct ft) (obj :: es).

  Definition Eoperator_call (oo : OverloadableOperator) (f : obj_name) (ft : type) (es : list Expr) : Expr :=
    Eoperator_call oo (operator_impl.Func f ft) es.

  Definition Eenum_const_at (gn : name) (c : ident) (ty : exprtype) : Expr :=
    Ecast (Cintegral ty) (Eenum_const gn c).

  Definition Ebuiltin (nm : obj_name) (ty : type) : Expr :=
    Ecast (Cbuiltin2fun $ Tptr ty) (Eglobal nm ty).

  Definition Emember (arrow : bool) (e_orig : Expr) (f : atomic_name_ type + name) (mut : bool) (ty : decltype) : force_some Expr :=
    option.get_some $
      match f with
      | inl f => Some $ Emember arrow e_orig f mut ty
      | inr on =>
          let e :=
            if arrow then
              match drop_qualifiers $ type_of e_orig with
              | Tptr t => Some (Ederef e_orig t)
              | _ => None
              end
            else
              Some e_orig
          in (fun e => Ecomma e (Eglobal on ty)) <$> e
      end.

  Definition Edefault_init_expr (e : Expr) : Expr := e.

End ParserExpr.
