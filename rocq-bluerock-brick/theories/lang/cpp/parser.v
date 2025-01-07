(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Ltac2.Ltac2.
Require Export bedrock.prelude.base.	(* for, e.g., <<::>> *)
Require Export bedrock.prelude.bytestring.	(* for <<%bs>> *)
Require Import bedrock.prelude.avl.
Require bedrock.prelude.funlist.

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
  Definition raw_alias_table : Type := NM.Raw.t type.

  #[global] Instance raw_structured_insert : forall {T}, Insert globname T (NM.Raw.t T) := _.

  #[projections(primitive)]
  Record t : Type := mk
    { r_symbols : raw_symbol_table
    ; r_types : raw_type_table
    ; r_aliases : raw_alias_table
    ; dups : list name }.

  Definition merge_obj_value (a b : ObjValue) : option ObjValue :=
    if sub_module.ObjValue_le a b then
      Some b
    else if sub_module.ObjValue_le b a then Some a
         else None.

  Definition _symbols (n : name) (v : ObjValue) : t -> t :=
    fun i =>
      match i.(r_symbols) !! n with
      | None => mk (<[n := v]> i.(r_symbols)) i.(r_types) i.(r_aliases) i.(dups)
      | Some v' => match merge_obj_value v v' with
                  | Some v => mk (<[n:=v]> i.(r_symbols)) i.(r_types) i.(r_aliases) i.(dups)
                  | None => mk i.(r_symbols) i.(r_types) i.(r_aliases) (n :: i.(dups))
                  end
      end.
  Definition merge_glob_decl (a b : GlobDecl) : option GlobDecl :=
    if sub_module.GlobDecl_le a b then
      Some b
    else if sub_module.GlobDecl_le b a then Some a
         else None.

  Definition _types (n : name) (v : GlobDecl) : t -> t :=
    fun i =>
      match i.(r_types) !! n with
      | None => mk i.(r_symbols) (<[n := v]> i.(r_types)) i.(r_aliases) i.(dups)
      | Some v' => match merge_glob_decl v v' with
                  | Some v => mk i.(r_symbols) (<[n:=v]> i.(r_types)) i.(r_aliases) i.(dups)
                  | None => mk i.(r_symbols) i.(r_types) i.(r_aliases) (n :: i.(dups))
                  end
      end.
  Definition _aliases (n : name) (v : type) : t -> t :=
    fun i =>
      match i.(r_aliases) !! n with
      | None => mk i.(r_symbols) i.(r_types) (<[n:=v]> i.(r_aliases)) i.(dups)
      | _ => mk i.(r_symbols) i.(r_types) i.(r_aliases) (n :: i.(dups))
      end.
  Definition _skip : t -> t := id.

  Variant which : Type :=
  | w_type (_ : name) (_ : GlobDecl)
  | w_symbol (_ : name) (_ : ObjValue)
  | w_alias (_ : name) (_ : type)
  | w_skip.

  Definition decls (p : _) : _ :=
    Eval cbv beta iota zeta delta [funlist.combine ] in
    funlist.combine (fun x => x) (fun (x : which) (a : t) => match x with
                                                       | w_type n g => _types n g a
                                                       | w_symbol n s => _symbols n s a
                                                       | w_alias n t => _aliases n t a
                                                       | w_skip => a
                                                       end) (mk ∅ ∅ ∅ nil) p.

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

    Definition make (ds : t) (e : endian) : translation_unit * list name :=
      pair {|
          symbols := NM.from_raw ds.(r_symbols);
          types := NM.from_raw ds.(r_types);
          aliases := NM.from_raw ds.(r_aliases);
          initializer := nil;	(** TODO *)
          byte_order := e;
        |} ds.(dups).

    (* [check_translation_unit tu]
     *)
    Ltac2 check_translation_unit (tu : preterm) (en : preterm) :=
      let endian := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype '(endian)) en in
      let tu := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype 't) tu in
      let term := Constr.Unsafe.make (Constr.Unsafe.App ('make) (Array.of_list [tu; endian])) in
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
#[local] Notation K := translation_unit.which (only parsing).

Definition Dvariable (n : obj_name) (t : type) (init : global_init.t lang.cpp) : K :=
  translation_unit.w_symbol n $ Ovar t init.

Definition Dfunction (n : obj_name) (f : Func) : K :=
  translation_unit.w_symbol n $ Ofunction f.

Definition Dmethod (n : obj_name) (static : bool) (f : Method) : K :=
  translation_unit.w_symbol n $ if static then Ofunction $ static_method f else Omethod f.

Definition Dconstructor (n : obj_name) (f : Ctor) : K :=
  translation_unit.w_symbol n $ Oconstructor f.

Definition Ddestructor (n : obj_name) (f : Dtor) : K :=
  translation_unit.w_symbol n $ Odestructor f.

Definition Dtype (n : globname) : K :=
  translation_unit.w_type n $ Gtype.

Definition Dunsupported (n : globname) (msg : bs) : K :=
  translation_unit.w_type n $ Gunsupported msg.

Definition Dstruct (n : globname) (f : option Struct) : K :=
  translation_unit.w_type n $ if f is Some f then Gstruct f else Gtype.

Definition Dunion (n : globname) (f : option Union) : K :=
  translation_unit.w_type n $ if f is Some f then Gunion f else Gtype.

Definition Denum (n : globname) (u : type) (cs : list ident) : K :=
  translation_unit.w_type n $ Genum u cs.

Definition Denum_constant (n : globname)
    (gn : globname) (ut : exprtype) (v : N + Z) (init : option Expr) : K :=
  translation_unit.w_type n $
  let v := match v with inl n => Echar n ut | inr z => Eint z ut end in
  let t := Tenum gn in
  Gconstant t $ Some $ Ecast (Cintegral t) v.

Definition Dignore : K :=
  translation_unit.w_skip.

Definition Dtypedef (n : globname) (t : type) : K :=
  translation_unit.w_alias n t.

Definition Dstatic_assert (msg : option bs) (e : Expr) : K :=
  translation_unit.w_skip.

Definition Qconst_volatile : type -> type := tqualified QCV.
Definition Qconst : type -> type := tqualified QC.
Definition Qvolatile : type -> type := tqualified QV.
