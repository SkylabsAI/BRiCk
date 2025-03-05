(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Ltac2.Ltac2.
Require Export bedrock.prelude.base.	(* for, e.g., <<::>> *)
Require Export Stdlib.Strings.PrimString.
Require Import bedrock.prelude.avl.
Require Export bedrock.lang.cpp.syntax. (* NOTE: too much *)
Require bedrock.lang.cpp.semantics.sub_module.
Require Export bedrock.lang.cpp.parser.stmt.
Require Import bedrock.lang.cpp.parser.lang.
Require Import bedrock.lang.cpp.parser.type.
Require Import bedrock.lang.cpp.parser.name.
Require Import bedrock.lang.cpp.parser.expr.
Require Import bedrock.lang.cpp.parser.decl.
Require Import bedrock.lang.cpp.parser.notation.
Require Import bedrock.lang.cpp.parser.reduction.

#[local] Definition parser_lang : lang.t := lang.cpp.
Include ParserName.
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

  #[global] Instance raw_structured_insert : forall {T}, Insert globname T (NM.Raw.t T) := _.

  Definition t : Type :=
    raw_symbol_table -> raw_type_table -> list name ->
    (raw_symbol_table -> raw_type_table -> list name -> translation_unit * list name) ->
    translation_unit * list name.

  Definition merge_obj_value (a b : ObjValue) : option ObjValue :=
    if sub_module.ObjValue_le a b then
      Some b
    else if sub_module.ObjValue_le b a then Some a
         else None.

  Definition _symbols (n : name) (v : ObjValue) : t :=
    fun s t dups k =>
      match s !! n with
      | None => k (<[n := v]> s) t dups
      | Some v' => match merge_obj_value v v' with
                  | Some v => k (<[n:=v]> s) t dups
                  | None => k s t (n :: dups)
                  end
      end.
  Definition merge_glob_decl (a b : GlobDecl) : option GlobDecl :=
    if sub_module.GlobDecl_le a b then
      Some b
    else if sub_module.GlobDecl_le b a then Some a
         else None.

  Definition _types (n : name) (v : GlobDecl) : t :=
    fun s t dups k =>
      if bool_decide (Gtypedef (Tnamed n) = v \/ Gtypedef (Tenum n) = v)
      then
        (* ignore self-aliases. These arise when you do
           something like
           <<
           typedef enum memory_order { .. } memory_order;
           >>
         *)
        k s t dups
      else
        match t !! n with
        | None => k s (<[n := v]> t) dups
        | Some v' => match merge_glob_decl v v' with
                    | Some v => k s (<[n:=v]> t) dups
                    | None => k s t (n :: dups)
                    end
        end.

  Definition _aliases (n : name) (ty : type) : t :=
    _types n (Gtypedef ty).

  Definition _skip : t :=
    fun s t dups k => k s t dups.

  Fixpoint decls' (ds : list t) : t :=
    match ds with
    | nil => fun s t dups k => k s t dups
    | d :: ds => fun s t dups k => d s t dups (fun s t dups' => decls' ds s t dups' k)
    end.

  Definition decls (ds : list t) (e : endian) : translation_unit * list name :=
    decls' ds ∅ ∅ [] $ fun s t => pair {|
      symbols := NM.from_raw s;
      types := NM.from_raw t;
      initializer := nil;	(** TODO *)
      byte_order := e;
    |}.

  (*
  Definition the_tu (result : translation_unit * list name)
    : match result.2 with
      | [] => translation_unit
      | _ => unit
      end :=
    match result.2 as X return match X with [] => translation_unit | _ => unit end with
    | [] => result.1
    | _ => tt
    end.
   *)

  Module make.
    Import Ltac2.Ltac2.

    Ltac2 Type exn ::= [DuplicateSymbols (constr)].

    (* [check_translation_unit tu]
     *)
    Ltac2 check_translation_unit (tu : preterm) (en : preterm) :=
      let endian := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype '(endian)) en in
      let tu := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype '(list t)) tu in
      let term := Constr.Unsafe.make (Constr.Unsafe.App ('decls) (Array.of_list [tu; endian])) in
      let rtu := Std.eval_vm None term in
      lazy_match! rtu with
      | pair ?tu nil => Std.exact_no_check tu
      | pair _ ?dups =>
          let _ := Message.print (Message.concat (Message.of_string "Duplicate symbols found in translation unit: ") (Message.of_constr dups)) in
          Control.throw (DuplicateSymbols dups)
      end.

  End make.

  Notation check tu en :=
    ltac2:(translation_unit.make.check_translation_unit tu en) (only parsing).

End translation_unit.
Export translation_unit(decls).
#[local] Notation K := translation_unit.t (only parsing).

Definition Dvariable (n : obj_name) (t : type) (init : global_init.t lang.cpp) : K :=
  _symbols n $ Ovar t init.

Definition Dfunction (n : obj_name) (f : Func) : K :=
  _symbols n $ Ofunction f.

Definition Dmethod (n : obj_name) (static : bool) (f : Method) : K :=
  _symbols n $ if static then Ofunction $ static_method f else Omethod f.

Definition Dconstructor (n : obj_name) (f : Ctor) : K :=
  _symbols n $ Oconstructor f.

Definition Ddestructor (n : obj_name) (f : Dtor) : K :=
  _symbols n $ Odestructor f.

Definition Dtype (n : globname) : K :=
  _types n $ Gtype.

Definition Dunsupported (n : globname) (msg : PrimString.string) : K :=
  _types n $ Gunsupported msg.

Definition Dstruct (n : globname) (f : option Struct) : K :=
  _types n $ if f is Some f then Gstruct f else Gtype.

Definition Dunion (n : globname) (f : option Union) : K :=
  _types n $ if f is Some f then Gunion f else Gtype.

Definition Denum (n : globname) (u : type) (cs : list ident) : K :=
  _types n $ Genum u cs.

Definition Denum_constant (n : globname)
    (gn : globname) (ut : exprtype) (v : N + Z) (init : option Expr) : K :=
  _types n $
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  Gconstant t $ Some $ Ecast (Cintegral t) v.

Definition Dtypedef (n : globname) (t : type) : K :=
  _aliases n t.

Definition Dstatic_assert (msg : option PrimString.string) (e : Expr) : K :=
  _skip.

Definition Qconst_volatile : type -> type := tqualified QCV.
Definition Qconst : type -> type := tqualified QC.
Definition Qvolatile : type -> type := tqualified QV.
