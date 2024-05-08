(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import elpi.apps.derive.std.	(* tag *)
Require Import bedrock.prelude.elpi.derive.
Require Import bedrock.prelude.compare.
Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.preliminary.
Require Import bedrock.lang.cpp.syntax.overloadable.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.stmt.
Require Import bedrock.lang.cpp.syntax.decl.

#[local] Set Primitive Projections.
#[local] Open Scope positive_scope.

Module sum.
  Section compare.
    Context {A B : Type}.
    Context (compareA : A -> A -> comparison).
    Context (compareB : B -> B -> comparison).
    Definition tag (s : A + B) : positive :=
      match s with
      | inl _ => 1
      | inr _ => 2
      end.
    Definition car (t : positive) : Type :=
      match t with
      | 1 => A
      | _ => B
      end.
    Definition data (s : A + B) : car (tag s) :=
      match s with
      | inl a => a
      | inr b => b
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => compareA
      | _ => compareB
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    Definition compare (s : A + B) : A + B -> comparison :=
      match s with
      | inl a => compare_ctor (Reduce (tag (inl a))) (fun _ => Reduce (data (inl a)))
      | inr b => compare_ctor (Reduce (tag (inr b))) (fun _ => Reduce (data (inr b)))
      end.

  End compare.
End sum.
#[global] Instance sum_compare `{!Compare A, !Compare B} : Compare (A + B) := sum.compare compare compare.

Module prod.
  Section compare.
    Context {A B : Type}.
    Context (compareA : A -> A -> comparison).
    Context (compareB : B -> B -> comparison).

    Definition compare (p1 p2 : A * B) : comparison :=
      match p1, p2 with
      | (a1, b1) , (a2 , b2) => compare_lex (compareA a1 a2) $ fun _ => compareB b1 b2
      end.
  End compare.
End prod.
#[global] Instance prod_compare `{!Compare A, !Compare B} : Compare (A * B) := prod.compare compare compare.

Module option.
  Section compare.
    Context {A : Type}.
    Context (compareA : A -> A -> comparison).

    Definition tag (o : option A) : positive :=
      match o with
      | Some _ => 1
      | None => 2
      end.
    Definition car (t : positive) : Type :=
      match t with
      | 1 => A
      | _ => unit
      end.
    Definition data (o : option A) : car (tag o) :=
      match o with
      | Some a => a
      | None => tt
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => compareA
      | _ => fun _ _ => Eq
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).
    #[local] Notation compare_tag := (compare_tag tag).

    Definition compare (x : option A) : option A -> comparison :=
      match x with
      | Some a => compare_ctor (Reduce (tag (Some a))) (fun _ => Reduce (data (Some a)))
      | None => compare_tag (Reduce (tag None))
      end.

  End compare.
End option.
#[global] Instance option_compare `{!Compare A} : Compare (option A) := option.compare compare.

Module List.
  Section compare.
    Context {A : Type}.
    Context (compareA : A -> A -> comparison).

    Record box_cons : Type := Box_cons {
      box_cons_0 : A;
      box_cons_1 : list A;
    }.
    Definition box_cons_compare (compareL : list A -> list A -> comparison)
        (b1 b2 : box_cons) : comparison :=
      compare_lex (compareA b1.(box_cons_0) b2.(box_cons_0)) $ fun _ =>
      compareL b1.(box_cons_1) b2.(box_cons_1).

    Definition tag (l : list A) : positive :=
      match l with
      | nil => 1
      | _ :: _ => 2
      end.
    Definition car (t : positive) : Type :=
      match t with
      | 1 => unit
      | _ => box_cons
      end.
    Definition data (l : list A) : car (tag l) :=
      match l with
      | nil => tt
      | x :: xs => Box_cons x xs
      end.
    Definition compare_data (compareL : list A -> list A -> comparison)
        (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => fun _ _ => Eq
      | _ => box_cons_compare compareL
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data).
    #[local] Notation compare_tag := (compare_tag tag).

    Fixpoint compare (l : list A) : list A -> comparison :=
      match l with
      | nil => compare_tag (Reduce (tag nil))
      | x :: xs => compare_ctor (compare_data compare) (Reduce (tag (x :: xs))) (fun _ => Reduce (data (x :: xs)))
      end.

  End compare.
End List.
#[global] Instance list_compare `{!Compare A} : Compare (list A) := List.compare compare.

Module ValCat.
  #[prefix="", only(tag)] derive ValCat.

  Definition compare (x y : ValCat) : comparison :=
    Pos.compare (tag x) (tag y).
End ValCat.
#[global] Instance ValCat_compare : Compare ValCat := ValCat.compare.

Module UnOp.
  #[prefix="", only(tag)] derive UnOp.
  Definition car (t : positive) : Set :=
    match t with
    | 5 => bs
    | _ => unit
    end.
  Definition data (x : UnOp) : car (tag x) :=
    match x with
    | Uunsupported msg => msg
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 5 => bs_cmp
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : UnOp) : UnOp -> comparison :=
    match op with
    | Uminus => compare_tag Uminus
    | Uplus => compare_tag Uplus
    | Unot => compare_tag Unot
    | Ubnot => compare_tag Ubnot
    | Uunsupported msg => compare_ctor (Uunsupported msg)
    end.

End UnOp.
#[global] Instance UnOp_compare : Compare UnOp := UnOp.compare.

Module BinOp.
  #[prefix="", only(tag)] derive BinOp.
  Definition car (t : positive) : Set :=
    match t with
    | 20 => bs
    | _ => unit
    end.
  Definition data (x : BinOp) : car (tag x) :=
    match x with
    | Bunsupported msg => msg
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 20 => bs_cmp
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : BinOp) : BinOp -> comparison :=
    match op with
    | Badd => compare_tag Badd
    | Band => compare_tag Band
    | Bcmp => compare_tag Bcmp
    | Bdiv => compare_tag Bdiv
    | Beq => compare_tag Beq
    | Bge => compare_tag Bge
    | Bgt => compare_tag Bgt
    | Ble => compare_tag Ble
    | Blt => compare_tag Blt
    | Bmul => compare_tag Bmul
    | Bneq => compare_tag Bneq
    | Bor => compare_tag Bor
    | Bmod => compare_tag Bmod
    | Bshl => compare_tag Bshl
    | Bshr => compare_tag Bshr
    | Bsub => compare_tag Bsub
    | Bxor => compare_tag Bxor
    | Bdotp => compare_tag Bdotp
    | Bdotip => compare_tag Bdotip
    | Bunsupported msg => compare_ctor (Bunsupported msg)
    end.

End BinOp.
#[global] Instance BinOp_compare : Compare BinOp := BinOp.compare.

Module RUnOp.
  #[prefix="", only(tag)] derive RUnOp.
  Definition car (t : positive) : Set :=
    match t with
    | 1 => UnOp
    | _ => unit
    end.
  Definition data (x : RUnOp) : car (tag x) :=
    match x with
    | Runop op => op
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 1 => UnOp.compare
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : RUnOp) : RUnOp -> comparison :=
    match op with
    | Runop op => compare_ctor (Runop op)
    | Rpreinc => compare_tag Rpreinc
    | Rpredec => compare_tag Rpredec
    | Rpostinc => compare_tag Rpostinc
    | Rpostdec => compare_tag Rpostdec
    | Rstar => compare_tag Rstar
    | Rarrow => compare_tag Rarrow
    end.

End RUnOp.
#[global] Instance RUnOp_compare : Compare RUnOp := RUnOp.compare.

Module RBinOp.
  #[prefix="", only(tag)] derive RBinOp.
  Definition car (t : positive) : Set :=
    match t with
    | 1 | 3 => BinOp
    | _ => unit
    end.
  Definition data (x : RBinOp) : car (tag x) :=
    match x with
    | Rbinop op | Rassign_op op => op
    | _ => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 1 | 3 => BinOp.compare
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : RBinOp) : RBinOp -> comparison :=
    match op with
    | Rbinop op => compare_ctor (Rbinop op)
    | Rassign => compare_tag Rassign
    | Rassign_op op => compare_ctor (Rassign_op op)
    | Rsubscript => compare_tag Rsubscript
    end.

End RBinOp.
#[global] Instance RBinOp_compare : Compare RBinOp := RBinOp.compare.

Module bitsize.
  #[prefix="", only(tag)] derive bitsize.

  Definition compare (x y : bitsize) : comparison :=
    Pos.compare (tag x) (tag y).
End bitsize.
#[global] Instance bitsize_compare : Compare bitsize := bitsize.compare.

Module signed.
  #[prefix="", only(tag)] derive signed.

  Definition compare (x y : signed) : comparison :=
    Pos.compare (tag x) (tag y).
End signed.
#[global] Instance signed_compare : Compare signed := signed.compare.

Module char_type.
  #[prefix="", only(tag)] derive char_type.t.

  Definition compare (x y : char_type.t) : comparison :=
    Pos.compare (tag x) (tag y).
End char_type.
#[global] Instance char_type_compare : Compare char_type.t := char_type.compare.

Module float_type.
  #[prefix="", only(tag)] derive float_type.t.

  Definition compare (x y : float_type.t) : comparison :=
    Pos.compare (tag x) (tag y).
End float_type.
#[global] Instance float_type_compare : Compare float_type.t := float_type.compare.

Module type_qualifiers.
  #[prefix="", only(tag)] derive type_qualifiers.

  Definition compare (x y : type_qualifiers) : comparison :=
    Pos.compare (tag x) (tag y).
End type_qualifiers.
#[global] Instance type_qualifiers_compare : Compare type_qualifiers := type_qualifiers.compare.

Module Cast.
  #[prefix="", only(tag)] derive Cast_.
  Section compare.
    Context {classname name type : Set}.
    Context (compareGN : classname -> classname -> comparison).
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    #[local] Notation Cast := (Cast_ classname name type).
    #[local] Notation TAG := (tag classname name type).

    Record box_Cdynamic : Set := Box_Cdynamic {
      box_Cdynamic_0 : classname;
      box_Cdynamic_1 : classname;
    }.
    Definition box_Cdynamic_compare (b1 b2 : box_Cdynamic) : comparison :=
      compare_lex (compareGN b1.(box_Cdynamic_0) b2.(box_Cdynamic_0)) $ fun _ =>
      compareGN b1.(box_Cdynamic_1) b2.(box_Cdynamic_1).

    Definition car (t : positive) : Set :=
      match t with
      | 10 | 11 => list classname
      | 20 => name
      | 21 | 24 => type
      | 22 => Cast
      | 23 => box_Cdynamic
      | _ => unit
      end.
    Definition data (c : Cast) : car (TAG c) :=
      match c with
      | Cderived2base ns | Cbase2derived ns => ns
      | Cuser n => n
      | Creinterpret t | Cconst t => t
      | Cstatic c => c
      | Cdynamic n1 n2 => Box_Cdynamic n1 n2
      | _ => ()
      end.
    Definition compare_data (Cast_compare : Cast -> Cast -> comparison)
        (t : positive) : car t -> car t -> comparison :=
      match t with
      | 10 | 11 => List.compare compareGN
      | 20 => compareN
      | 21 | 24 => compareT
      | 22 => Cast_compare
      | 23 => box_Cdynamic_compare
      | _ => fun _ _ => Eq
      end.

    #[local] Notation compare_ctor := (compare_ctor TAG car data).
    #[local] Notation compare_tag := (compare_tag TAG).

    Fixpoint compare (c : Cast) : Cast -> comparison :=
      match c with
      | Cbitcast => compare_tag (Reduce (TAG Cbitcast))
      | Clvaluebitcast => compare_tag (Reduce (TAG Clvaluebitcast))
      | Cl2r => compare_tag (Reduce (TAG Cl2r))
      | Cnoop => compare_tag (Reduce (TAG Cnoop))
      | Carray2ptr => compare_tag (Reduce (TAG Carray2ptr))
      | Cfun2ptr => compare_tag (Reduce (TAG Cfun2ptr))
      | Cint2ptr => compare_tag (Reduce (TAG Cint2ptr))
      | Cptr2int => compare_tag (Reduce (TAG Cptr2int))
      | Cptr2bool => compare_tag (Reduce (TAG Cptr2bool))
      | Cderived2base ns => compare_ctor (compare_data compare) (Reduce (TAG (Cderived2base ns))) (fun _ => Reduce (data (Cderived2base ns)))
      | Cbase2derived ns => compare_ctor (compare_data compare) (Reduce (TAG (Cderived2base ns))) (fun _ => Reduce (data (Cbase2derived ns)))
      | Cintegral => compare_tag (Reduce (TAG Cintegral))
      | Cint2bool => compare_tag (Reduce (TAG Cint2bool))
      | Cfloat2int => compare_tag (Reduce (TAG Cfloat2int))
      | Cnull2ptr => compare_tag (Reduce (TAG Cnull2ptr))
      | Cnull2memberptr => compare_tag (Reduce (TAG Cnull2memberptr))
      | Cbuiltin2fun => compare_tag (Reduce (TAG Cbuiltin2fun))
      | Cctor => compare_tag (Reduce (TAG Cctor))
      | C2void => compare_tag (Reduce (TAG C2void))
      | Cuser n => compare_ctor (compare_data compare) (Reduce (TAG (Cuser n))) (fun _ => Reduce (data (Cuser n)))
      | Creinterpret t => compare_ctor (compare_data compare) (Reduce (TAG (Creinterpret t))) (fun _ => Reduce (data (Creinterpret t)))
      | Cstatic c => compare_ctor (compare_data compare) (Reduce (TAG (Cstatic c))) (fun _ => Reduce (data (Cstatic c)))
      | Cdynamic cls1 cls2 => compare_ctor (compare_data compare) (Reduce (TAG (Cdynamic cls1 cls2))) (fun _ => Reduce (data (Cdynamic cls1 cls2)))
      | Cconst t => compare_ctor (compare_data compare) (Reduce (TAG (Cconst t))) (fun _ => Reduce (data (Cconst t)))
      end.
  End compare.

End Cast.
#[global] Instance Cast_compare {A B C : Set} `{!Compare A, !Compare B, !Compare C} : Compare (Cast_ A B C) := Cast.compare compare compare compare.


Module dispatch_type.
  #[prefix="", only(tag)] derive dispatch_type.

  Definition compare (x y : dispatch_type) : comparison :=
    Pos.compare (tag x) (tag y).
End dispatch_type.
#[global] Instance dispatch_type_compare : Compare dispatch_type := dispatch_type.compare.

Module MethodRef.
  Section compare.
    Context {obj_name functype Expr : Set}.
    Context (compareON : obj_name -> obj_name -> comparison).
    Context (compareFT : functype -> functype -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    #[local] Notation MethodRef := (MethodRef_ obj_name functype Expr).

    Definition compare : MethodRef -> MethodRef -> comparison :=
      sum.compare (
        fun '(n1, d1, t1) '(n2, d2, t2) =>
        compare_lex (compareON n1 n2) $ fun _ =>
        compare_lex (dispatch_type.compare d1 d2) $ fun _ =>
        compareFT t1 t2
      ) compareE.
  End compare.
End MethodRef.
#[global] Hint Opaque MethodRef_ : typeclass_instances.
#[global] Instance MethodRef_compare {A B C : Set} `{!Compare A, !Compare B, !Compare C} : Compare (MethodRef_ A B C) := MethodRef.compare compare compare compare.

Module operator_impl.
  Export preliminary.operator_impl.

  Section compare.
    Context {obj_name type : Set}.
    Context (compareON : obj_name -> obj_name -> comparison).
    Context (compareT : type -> type -> comparison).
    #[local] Notation t := (t obj_name type).

    Record box_Func : Set := Box_Func {
      box_Func_0 : obj_name;
      box_Func_1 : type;
    }.
    Definition box_Func_compare  (b1 b2 : box_Func) : comparison :=
      compare_lex (compareON b1.(box_Func_0) b2.(box_Func_0)) $ fun _ =>
      compareT b1.(box_Func_1) b2.(box_Func_1).

    Record box_MFunc : Set := Box_MFunc {
      box_MFunc_0 : obj_name;
      box_MFunc_1 : dispatch_type;
      box_MFunc_2 : type;
    }.
    Definition box_MFunc_compare (b1 b2 : box_MFunc) : comparison :=
      compare_lex (compareON b1.(box_MFunc_0) b2.(box_MFunc_0)) $ fun _ =>
      compare_lex (dispatch_type.compare b1.(box_MFunc_1) b2.(box_MFunc_1)) $ fun _ =>
      compareT b1.(box_MFunc_2) b2.(box_MFunc_2).

    Definition tag (p : t) : positive :=
      match p with
      | Func _ _ => 1
      | MFunc _ _ _ => 2
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => box_Func
      | _ => box_MFunc
      end.
    Definition data (p : t) : car (tag p) :=
      match p with
      | Func on t => Box_Func on t
      | MFunc on d t => Box_MFunc on d t
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => box_Func_compare
      | _ => box_MFunc_compare
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    Definition compare (p : t) : t -> comparison :=
      match p with
      | Func on t => compare_ctor (Reduce (tag (Func on t))) (fun _ => Reduce (data (Func on t)))
      | MFunc on d t => compare_ctor (Reduce (tag (MFunc on d t))) (fun _ => Reduce (data (MFunc on d t)))
      end.
  End compare.

End operator_impl.
#[global] Instance operator_impl_compare {A B : Set} `{!Compare A, !Compare B} : Compare (operator_impl.t A B) := operator_impl.compare compare compare.

Module AtomicOp.
  #[prefix="", only(tag)] derive AtomicOp.

  Definition compare (x y : AtomicOp) : comparison :=
    Pos.compare (tag x) (tag y).
End AtomicOp.
#[global] Instance AtomicOp_compare : Compare AtomicOp := AtomicOp.compare.

Module calling_conv.
  #[prefix="", only(tag)] derive calling_conv.

  Definition compare (x y : calling_conv) : comparison :=
    Pos.compare (tag x) (tag y).
End calling_conv.
#[global] Instance calling_conv_compare : Compare calling_conv := calling_conv.compare.

Module function_arity.
  #[prefix="", only(tag)] derive function_arity.

  Definition compare (x y : function_arity) : comparison :=
    Pos.compare (tag x) (tag y).
End function_arity.
#[global] Instance function_arity_compare : Compare function_arity := function_arity.compare.

Module new_form.
  Export preliminary.new_form.

  #[prefix="", only(tag)] derive t.
  Definition car (t : positive) : Set :=
    match t with
    | 1 => bool
    | _ => unit
    end.
  Definition data (x : new_form) : car (tag x) :=
    match x with
    | Allocating b => b
    | NonAllocating => ()
    end.
  Definition compare_data (t : positive) : car t -> car t -> comparison :=
    match t with
    | 1 => Bool.compare
    | _ => fun _ _ => Eq
    end.

  #[local] Tactic Notation "compare_ctor" uconstr(x) :=
    let t := eval red in (tag x) in
    let d := eval red in (data x) in
    exact (compare_ctor tag car data compare_data t (fun _ => d)).
  #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
  #[local] Tactic Notation "compare_tag" uconstr(x) :=
    let t := eval red in (tag x) in
    exact (fun y => Pos.compare t (tag y)).
  #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

  Definition compare (op : new_form) : new_form -> comparison :=
    match op with
    | Allocating b => compare_ctor (Allocating b)
    | NonAllocating => compare_tag NonAllocating
    end.

End new_form.
#[global] Instance new_form_compare : Compare new_form := new_form.compare.

Module function_type.

  Definition compare {type : Set} (compareT : type -> type -> comparison)
      (x y : function_type_ type) : comparison :=
    compare_lex (calling_conv.compare x.(ft_cc) y.(ft_cc)) $ fun _ =>
    compare_lex (function_arity.compare x.(ft_arity) y.(ft_arity)) $ fun _ =>
    compare_lex (compareT x.(ft_return) y.(ft_return)) $ fun _ =>
    List.compare compareT x.(ft_params) y.(ft_params).

End function_type.
#[global] Instance function_type_compare {A : Set} `{!Compare A} : Compare (function_type_ A) := function_type.compare compare.

Module temp_param.
  Section compare.
    Context {type : Set}.
    Context (compareT : type -> type -> comparison).
    #[local] Notation temp_param := (temp_param_ type).

    Record box_Pvalue : Set := Box_Pvalue {
      box_Pvalue_0 : ident;
      box_Pvalue_1 : type;
    }.
    Definition box_Pvalue_compare (b1 b2 : box_Pvalue) : comparison :=
      compare_lex (bs_cmp b1.(box_Pvalue_0) b2.(box_Pvalue_0)) $ fun _ =>
      compareT b1.(box_Pvalue_1) b2.(box_Pvalue_1).

    Definition tag (p : temp_param) : positive :=
      match p with
      | Ptype _ => 1
      | Pvalue _ _ => 2
      | Punsupported _ => 3
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 2 => box_Pvalue
      | _ => bs
      end.
    Definition data (p : temp_param) : car (tag p) :=
      match p with
      | Ptype id => id
      | Pvalue id t => Box_Pvalue id t
      | Punsupported msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 2 => box_Pvalue_compare
      | _ => bs_cmp
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    Definition compare (p : temp_param_ type) : temp_param_ type -> comparison :=
      match p with
      | Ptype id => compare_ctor (Reduce (tag (Ptype id))) (fun _ => Reduce (data (Ptype id)))
      | Pvalue id ty => compare_ctor (Reduce (tag (Pvalue id ty))) (fun _ => Reduce (data (Pvalue id ty)))
      | Punsupported msg => compare_ctor (Reduce (tag (Punsupported msg))) (fun _ => Reduce (data (Punsupported msg)))
      end.
  End compare.

End temp_param.
#[global] Instance temp_param_compare {A : Set} `{!Compare A} : Compare (temp_param_ A) := temp_param.compare compare.

Module temp_arg.
  Section compare.
    Context {type Expr : Set}.
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    #[local] Notation temp_arg := (temp_arg_ type Expr).

    Definition tag (p : temp_arg) : positive :=
      match p with
      | Atype _ => 1
      | Avalue _ => 2
      | Aunsupported _ => 3
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => type
      | 2 => Expr
      | _ => bs
      end.
    Definition data (p : temp_arg) : car (tag p) :=
      match p with
      | Atype t => t
      | Avalue e => e
      | Aunsupported msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => compareT
      | 2 => compareE
      | _ => bs_cmp
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    Definition compare (p : temp_arg) : temp_arg -> comparison :=
      match p with
      | Atype t => compare_ctor (Reduce (tag (Atype t))) (fun _ => Reduce (data (Atype t)))
      | Avalue e => compare_ctor (Reduce (tag (Avalue e))) (fun _ => Reduce (data (Avalue e)))
      | Aunsupported msg => compare_ctor (Reduce (tag (Aunsupported msg))) (fun _ => Reduce (data (Aunsupported msg)))
      end.
  End compare.

End temp_arg.
#[global] Instance temp_arg_compare {A B : Set} `{!Compare A, !Compare B} : Compare (temp_arg_ A B) := temp_arg.compare compare compare.

Module OverloadableOperator.
  #[prefix="", only(tag)] derive OverloadableOperator.

  Section compare.
    #[local] Notation OO := OverloadableOperator.

    Definition car (t : positive) : Set :=
      match t with
      | 39 | 40 => bool
      | _ => unit
      end.
    Definition data (p : OO) : car (tag p) :=
      match p with
      | OONew b | OODelete b => b
      | _ => tt
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 39 | 40 => Bool.compare
      | _ => fun _ _ => Eq
      end.

    #[local] Tactic Notation "compare_ctor" uconstr(x) :=
      let t := eval red in (tag x) in
      let d := eval red in (data x) in
      exact (compare_ctor tag car data compare_data t (fun _ => d)).
    #[local] Notation compare_ctor x := ltac:(compare_ctor x) (only parsing).
    #[local] Tactic Notation "compare_tag" uconstr(x) :=
      let t := eval red in (tag x) in
      exact (fun y => Pos.compare t (tag y)).
    #[local] Notation compare_tag x := ltac:(compare_tag x) (only parsing).

    Definition compare (oo : OO) : OO -> comparison :=
      match oo with
      | OOTilde => compare_tag OOTilde
      | OOExclaim => compare_tag OOExclaim
      | OOPlusPlus => compare_tag OOPlusPlus
      | OOMinusMinus => compare_tag OOMinusMinus
      | OOStar => compare_tag OOStar
      | OOPlus => compare_tag OOPlus
      | OOMinus => compare_tag OOMinus
      | OOSlash => compare_tag OOSlash
      | OOPercent => compare_tag OOPercent
      | OOCaret => compare_tag OOCaret
      | OOAmp => compare_tag OOAmp
      | OOPipe => compare_tag OOPipe
      | OOEqual => compare_tag OOEqual
      | OOLessLess => compare_tag OOLessLess
      | OOGreaterGreater => compare_tag OOGreaterGreater
      | OOPlusEqual => compare_tag OOPlusEqual
      | OOMinusEqual => compare_tag OOMinusEqual
      | OOStarEqual => compare_tag OOStarEqual
      | OOSlashEqual => compare_tag OOSlashEqual
      | OOPercentEqual => compare_tag OOPercentEqual
      | OOCaretEqual => compare_tag OOCaretEqual
      | OOAmpEqual => compare_tag OOAmpEqual
      | OOPipeEqual => compare_tag OOPipeEqual
      | OOLessLessEqual => compare_tag OOLessLessEqual
      | OOGreaterGreaterEqual => compare_tag OOGreaterGreaterEqual
      | OOEqualEqual => compare_tag OOEqualEqual
      | OOExclaimEqual => compare_tag OOExclaimEqual
      | OOLess => compare_tag OOLess
      | OOGreater => compare_tag OOGreater
      | OOLessEqual => compare_tag OOLessEqual
      | OOGreaterEqual => compare_tag OOGreaterEqual
      | OOSpaceship => compare_tag OOSpaceship
      | OOComma => compare_tag OOComma
      | OOArrowStar => compare_tag OOArrowStar
      | OOArrow => compare_tag OOArrow
      | OOSubscript => compare_tag OOSubscript
      | OOAmpAmp => compare_tag OOAmpAmp
      | OOPipePipe => compare_tag OOPipePipe
      | OONew b => compare_ctor (OONew b)
      | OODelete b => compare_ctor (OODelete b)
      | OOCall => compare_tag OOCall
      | OOCoawait => compare_tag OOCoawait
      end.
  End compare.

End OverloadableOperator.
#[global] Instance OverloadableOperator_compare : Compare OverloadableOperator := OverloadableOperator.compare.

Module function_name.
  Section compare.
    Context {type : Set}.
    Context (compareT : type -> type -> comparison).
    #[local] Notation function_name := (function_name_ type).

    Definition tag (x : function_name) : positive :=
      match x with
      | Nf _ => 1
      | Nctor => 2
      | Ndtor => 3
      | Nop _ => 4
      | Nop_conv _ => 5
      | Nop_lit _ => 6
      | Nunsupported_function _ => 7
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 | 6 | 7 => bs
      | 4 => OverloadableOperator
      | 5 => type
      | _ => unit
      end.
    Definition data (x : function_name) : car (tag x) :=
      match x with
      | Nf f => f
      | Nctor
      | Ndtor => ()
      | Nop oo => oo
      | Nop_conv t => t
      | Nop_lit id => id
      | Nunsupported_function msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 | 6 | 7 => bs_cmp
      | 4 => OverloadableOperator.compare
      | 5 => compareT
      | _ => fun _ _ => Eq
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).
    #[local] Notation compare_tag := (compare_tag tag).

    Definition compare (x : function_name) : function_name -> comparison :=
      match x with
      | Nf f => compare_ctor (Reduce (tag (Nf f))) (fun _ => Reduce (data (Nf f)))
      | Nctor => compare_tag (Reduce (tag Nctor))
      | Ndtor => compare_tag (Reduce (tag Ndtor))
      | Nop oo => compare_ctor (Reduce (tag (Nop oo))) (fun _ => Reduce (data (Nop oo)))
      | Nop_conv t => compare_ctor (Reduce (tag (Nop_conv t))) (fun _ => Reduce (data (Nop_conv t)))
      | Nop_lit id => compare_ctor (Reduce (tag (Nop_lit id))) (fun _ => Reduce (data (Nop_lit id)))
      | Nunsupported_function msg => compare_ctor (Reduce (tag (Nunsupported_function msg))) (fun _ => Reduce (data (Nunsupported_function msg)))
      end.
  End compare.

End function_name.
#[global] Instance function_name_compare {A : Set} `{!Compare A} : Compare (function_name_ A) := function_name.compare compare.

Module function_qualifier.
  #[prefix="", only(tag)] derive function_qualifier.

  Definition compare (x y : function_qualifier) : comparison :=
    Pos.compare (tag x) (tag y).
End function_qualifier.
#[global] Instance function_qualifier_compare : Compare function_qualifier := function_qualifier.compare.

Module atomic_name.
  #[prefix="", only(tag)] derive atomic_name_.
  #[global] Arguments tag {_} & _ : assert.
  Section compare.
    Context {type Expr : Set}.
    Context (compareT : type -> type -> comparison).
    #[local] Notation atomic_name := (atomic_name_ type).
    #[local] Notation tag := (@tag type).

    Record box_Nfunction : Set := Box_Nfunction {
      box_Nfunction_0 : list function_qualifier;
      box_Nfunction_1 : function_name_ type;
      box_Nfunction_2 : list type;
    }.
    Definition box_Nfunction_compare (b1 b2 : box_Nfunction) : comparison :=
      compare_lex (List.compare function_qualifier.compare b1.(box_Nfunction_0) b2.(box_Nfunction_0)) $ fun _ =>
      compare_lex (function_name.compare compareT b1.(box_Nfunction_1) b2.(box_Nfunction_1)) $ fun _ =>
      List.compare compareT b1.(box_Nfunction_2) b2.(box_Nfunction_2).

    Definition car (t : positive) : Set :=
      match t with
      | 1 => bs
      | 2 => box_Nfunction
      | 3 => list type
      | 4 => N
      | _ => bs
      end.
    Definition data (p : atomic_name) : car (tag p) :=
      match p with
      | Nid id => id
      | Nfunction qs f ts => Box_Nfunction qs f ts
      | Nclosure ts => ts
      | Nanon n => n
      | Nunsupported_atomic msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => bs_cmp
      | 2 => box_Nfunction_compare
      | 3 => List.compare compareT
      | 4 => N.compare
      | _ => bs_cmp
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).

    Definition compare (p : atomic_name) : atomic_name -> comparison :=
      match p with
      | Nid i => compare_ctor (Reduce (tag (Nid i))) (fun _ => Reduce (data (Nid i)))
      | Nfunction qs f ts => compare_ctor (Reduce (tag (Nfunction qs f ts))) (fun _ => Reduce (data (Nfunction qs f ts)))
      | Nclosure ts => compare_ctor (Reduce (tag (Nclosure ts))) (fun _ => Reduce (data (Nclosure ts)))
      | Nanon n => compare_ctor (Reduce (tag (Nanon n))) (fun _ => Reduce (data (Nanon n)))
      | Nunsupported_atomic msg => compare_ctor (Reduce (tag (Nunsupported_atomic msg))) (fun _ => Reduce (data (Nunsupported_atomic msg)))
      end.
  End compare.

End atomic_name.
#[global] Instance atomic_name_compare {A : Set} `{!Compare A} : Compare (atomic_name_ A) := atomic_name.compare compare.

Module name.
  Section compare_body.
    Context {lang : lang.t}.
    #[local] Notation name := (name' lang).
    #[local] Notation type := (type' lang).
    #[local] Notation Expr := (Expr' lang).
    #[local] Notation atomic_name := (atomic_name' lang).
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).

    Record box_Ninst : Set := Box_Ninst {
      box_Ninst_0 : name;
      box_Ninst_1 : list (temp_arg' lang);
    }.
    Definition box_Ninst_compare (b1 b2 : box_Ninst) : comparison :=
      compare_lex (compareN b1.(box_Ninst_0) b2.(box_Ninst_0)) $ fun _ =>
      List.compare (temp_arg.compare compareT compareE) b1.(box_Ninst_1) b2.(box_Ninst_1).

    Record box_Nscoped : Set := Box_Nscoped {
      box_Nscoped_0 : name;
      box_Nscoped_1 : atomic_name;
    }.
    Definition box_Nscoped_compare (b1 b2 : box_Nscoped) : comparison :=
      compare_lex (compareN b1.(box_Nscoped_0) b2.(box_Nscoped_0)) $ fun _ =>
      atomic_name.compare compareT b1.(box_Nscoped_1) b2.(box_Nscoped_1).

    Definition tag (n : name) : positive :=
      match n with
      | Ninst _ _ => 1
      | Nglobal _ => 2
      | Ndependent _ => 3
      | Nscoped _ _ => 4
      | _ => 5
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => box_Ninst
      | 2 => atomic_name
      | 3 => type
      | 4 => box_Nscoped
      | _ => bs
      end.
    Definition data (n : name) : car (tag n) :=
      match n with
      | Ninst n args => Box_Ninst n args
      | Nglobal c => c
      | Ndependent t => t
      | Nscoped n c => Box_Nscoped n c
      | Nunsupported msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => box_Ninst_compare
      | 2 => atomic_name.compare compareT
      | 3 => compareT
      | 4 => box_Nscoped_compare
      | _ => bs_cmp
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).
    Definition compare_body (n : name) : name -> comparison :=
      match n with
      | Ninst t xs => compare_ctor (Reduce (tag (Ninst t xs))) (fun _ => Reduce (data (Ninst t xs)))
      | Nglobal c => compare_ctor (Reduce (tag (Nglobal c))) (fun _ => Reduce (data (Nglobal c)))
      | Ndependent t => compare_ctor (Reduce (tag (Ndependent t))) (fun _ => Reduce (data (Ndependent t)))
      | Nscoped n c => compare_ctor (Reduce (tag (Nscoped n c))) (fun _ => Reduce (data (Nscoped n c)))
      | Nunsupported msg => compare_ctor (Reduce (tag (Nunsupported msg))) (fun _ => Reduce (data (Nunsupported msg)))
      end.
  End compare_body.
End name.

Module type.
  Section compare_body.
    Context {lang : lang.t}.
    #[local] Notation name := (name' lang).
    #[local] Notation type := (type' lang).
    #[local] Notation Expr := (Expr' lang).
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).


    Record box_Tresult_unop : Set := Box_Tresult_unop {
      box_Tresult_unop_0 : RUnOp;
      box_Tresult_unop_1 : type;
    }.
    Definition box_Tresult_unop_compare (b1 b2 : box_Tresult_unop) : comparison :=
      compare_lex (RUnOp.compare b1.(box_Tresult_unop_0) b2.(box_Tresult_unop_0)) $ fun _ =>
      compareT b1.(box_Tresult_unop_1) b2.(box_Tresult_unop_1).

    Record box_Tresult_binop : Set := Box_Tresult_binop {
      box_Tresult_binop_0 : RBinOp;
      box_Tresult_binop_1 : type;
      box_Tresult_binop_2 : type;
    }.
    Definition box_Tresult_binop_compare (b1 b2 : box_Tresult_binop) : comparison :=
      compare_lex (RBinOp.compare b1.(box_Tresult_binop_0) b2.(box_Tresult_binop_0)) $ fun _ =>
      compare_lex (compareT b1.(box_Tresult_binop_1) b2.(box_Tresult_binop_1)) $ fun _ =>
      compareT b1.(box_Tresult_binop_2) b2.(box_Tresult_binop_2).

    Record box_Tresult_call : Set := Box_Tresult_call {
      box_Tresult_call_0 : name;
      box_Tresult_call_1 : list type;
    }.
    Definition box_Tresult_call_compare (b1 b2 : box_Tresult_call) : comparison :=
      compare_lex (compareN b1.(box_Tresult_call_0) b2.(box_Tresult_call_0)) $ fun _ =>
      List.compare compareT b1.(box_Tresult_call_1) b2.(box_Tresult_call_1).

    Record box_Tresult_member_call : Set := Box_Tresult_member_call {
      box_Tresult_member_call_0 : name;
      box_Tresult_member_call_1 : type;
      box_Tresult_member_call_2 : list type;
    }.
    Definition box_Tresult_member_call_compare (b1 b2 : box_Tresult_member_call) : comparison :=
      compare_lex (compareN b1.(box_Tresult_member_call_0) b2.(box_Tresult_member_call_0)) $ fun _ =>
      compare_lex (compareT b1.(box_Tresult_member_call_1) b2.(box_Tresult_member_call_1)) $ fun _ =>
      List.compare compareT b1.(box_Tresult_member_call_2) b2.(box_Tresult_member_call_2).

    Record box_Tresult_parenlist : Set := Box_Tresult_parenlist {
      box_Tresult_parenlist_0 : type;
      box_Tresult_parenlist_1 : list type;
    }.
    Definition box_Tresult_parenlist_compare (b1 b2 : box_Tresult_parenlist) : comparison :=
      compare_lex (compareT b1.(box_Tresult_parenlist_0) b2.(box_Tresult_parenlist_0)) $ fun _ =>
      List.compare compareT b1.(box_Tresult_parenlist_1) b2.(box_Tresult_parenlist_1).

    Record box_Tresult_member : Set := Box_Tresult_member {
      box_Tresult_member_0 : type;
      box_Tresult_member_1 : ident;
    }.
    Definition box_Tresult_member_compare (b1 b2 : box_Tresult_member) : comparison :=
      compare_lex (compareT b1.(box_Tresult_member_0) b2.(box_Tresult_member_0)) $ fun _ =>
      bs_cmp b1.(box_Tresult_member_1) b2.(box_Tresult_member_1).

    Record box_Tnum : Set := Box_Tnum {
      box_Tnum_0 : bitsize;
      box_Tnum_1 : signed;
    }.
    Definition box_Tnum_compare (b1 b2 : box_Tnum) : comparison :=
      compare_lex (bitsize.compare b1.(box_Tnum_0) b2.(box_Tnum_0)) $ fun _ =>
      signed.compare b1.(box_Tnum_1) b2.(box_Tnum_1).

    Record box_Tarray : Set := Box_Tarray {
      box_Tarray_0 : type;
      box_Tarray_1 : N;
    }.
    Definition box_Tarray_compare (b1 b2 : box_Tarray) : comparison :=
      compare_lex (compareT b1.(box_Tarray_0) b2.(box_Tarray_0)) $ fun _ =>
      N.compare b1.(box_Tarray_1) b2.(box_Tarray_1).

    Record box_Tvariable_array : Set := Box_Tvariable_array {
      box_Tvariable_array_0 : type;
      box_Tvariable_array_1 : Expr;
    }.
    Definition box_Tvariable_array_compare (b1 b2 : box_Tvariable_array) : comparison :=
      compare_lex (compareT b1.(box_Tvariable_array_0) b2.(box_Tvariable_array_0)) $ fun _ =>
      compareE b1.(box_Tvariable_array_1) b2.(box_Tvariable_array_1).

    Record box_Tmember_pointer : Set := Box_Tmember_pointer {
      box_Tmember_pointer_0 : name;
      box_Tmember_pointer_1 : type;
    }.
    Definition box_Tmember_pointer_compare (b1 b2 : box_Tmember_pointer) : comparison :=
      compare_lex (compareN b1.(box_Tmember_pointer_0) b2.(box_Tmember_pointer_0)) $ fun _ =>
      compareT b1.(box_Tmember_pointer_1) b2.(box_Tmember_pointer_1).

    Record box_Tqualified : Set := Box_Tqualified {
      box_Tqualified_0 : type_qualifiers;
      box_Tqualified_1 : type;
    }.
    Definition box_Tqualified_compare (b1 b2 : box_Tqualified) : comparison :=
      compare_lex (type_qualifiers.compare b1.(box_Tqualified_0) b2.(box_Tqualified_0)) $ fun _ =>
      compareT b1.(box_Tqualified_1) b2.(box_Tqualified_1).

    Record box_Tarch : Set := Box_Tarch {
      box_Tarch_0 : option bitsize;
      box_Tarch_1 : bs;
    }.
    Definition box_Tarch_compare (b1 b2 : box_Tarch) : comparison :=
      compare_lex (option.compare bitsize.compare b1.(box_Tarch_0) b2.(box_Tarch_0)) $ fun _ =>
      bs_cmp b1.(box_Tarch_1) b2.(box_Tarch_1).

    Definition tag (t : type) : positive :=
      match t with
      | Tparam _ => 1
      | Tresult_param _ => 2
      | Tresult_global _ => 3
      | Tresult_unop _ _ => 4
      | Tresult_binop _ _ _ => 5
      | Tresult_call _ _ => 6
      | Tresult_member_call _ _ _ => 7
      | Tresult_parenlist _ _ => 8
      | Tresult_member _ _ => 9
      | Tptr _ => 10
      | Tref _ => 11
      | Trv_ref _ => 12
      | Tnum _ _ => 13
      | Tchar_ _ => 14
      | Tvoid => 15
      | Tarray _ _ => 16
      | Tincomplete_array _ => 17
      | Tvariable_array _ _ => 18
      | Tnamed _ => 19
      | Tenum _ => 20
      | Tfunction _ => 21
      | Tbool => 22
      | Tmember_pointer _ _ => 23
      | Tfloat_ _ => 24
      | Tqualified _ _ => 25
      | Tnullptr => 26
      | Tarch _ _ => 27
      | Tdecltype _ => 28
      | Tunsupported _ => 29
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 | 2 => ident
      | 3 => name
      | 4 => box_Tresult_unop
      | 5 => box_Tresult_binop
      | 6 => box_Tresult_call
      | 7 => box_Tresult_member_call
      | 8 => box_Tresult_parenlist
      | 9 => box_Tresult_member
      | 10 | 11 | 12 => type
      | 13 => box_Tnum
      | 14 => char_type
      | 15 => unit
      | 16 => box_Tarray
      | 17 => type
      | 18 => box_Tvariable_array
      | 19 | 20 => name
      | 21 => function_type_ type
      | 22 => unit
      | 23 => box_Tmember_pointer
      | 24 => float_type.t
      | 25 => box_Tqualified
      | 26 => unit
      | 27 => box_Tarch
      | 28 => Expr
      | _ => bs
      end.
    Definition data (t : type) : car (tag t) :=
      match t with
      | Tparam T => T
      | Tresult_param X => X
      | Tresult_global on => on
      | Tresult_unop op t => Box_Tresult_unop op t
      | Tresult_binop op tl tr => Box_Tresult_binop op tl tr
      | Tresult_call on ts => Box_Tresult_call on ts
      | Tresult_member_call on t ts => Box_Tresult_member_call on t ts
      | Tresult_parenlist t ts => Box_Tresult_parenlist t ts
      | Tresult_member t f => Box_Tresult_member t f
      | Tptr t | Tref t | Trv_ref t => t
      | Tnum sz sgn => Box_Tnum sz sgn
      | Tchar_ t => t
      | Tvoid => ()
      | Tarray t n => Box_Tarray t n
      | Tincomplete_array t => t
      | Tvariable_array t e => Box_Tvariable_array t e
      | Tnamed gn | Tenum gn => gn
      | Tfunction t => t
      | Tbool => ()
      | Tmember_pointer gn t => Box_Tmember_pointer gn t
      | Tfloat_ t => t
      | Tqualified cv t => Box_Tqualified cv t
      | Tnullptr => ()
      | Tarch sz n => Box_Tarch sz n
      | Tdecltype e => e
      | Tunsupported msg => msg
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 | 2 => bs_cmp
      | 3 => compareN
      | 4 => box_Tresult_unop_compare
      | 5 => box_Tresult_binop_compare
      | 6 => box_Tresult_call_compare
      | 7 => box_Tresult_member_call_compare
      | 8 => box_Tresult_parenlist_compare
      | 9 => box_Tresult_member_compare
      | 10 | 11 | 12 => compareT
      | 13 => box_Tnum_compare
      | 14 => char_type.compare
      | 15 => fun _ _ => Eq
      | 16 => box_Tarray_compare
      | 17 => compareT
      | 18 => box_Tvariable_array_compare
      | 19 | 20 => compareN
      | 21 => function_type.compare compareT
      | 22 => fun _ _ => Eq
      | 23 => box_Tmember_pointer_compare
      | 24 => float_type.compare
      | 25 => box_Tqualified_compare
      | 26 => fun _ _ => Eq
      | 27 => box_Tarch_compare
      | 28 => compareE
      | _ => bs_cmp
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).
    #[local] Notation compare_tag := (compare_tag tag).

    Definition compare_body (t : type) : type -> comparison :=
      match t with
      | Tparam T => compare_ctor (Reduce (tag (Tparam T))) (fun _ => Reduce (data (Tparam T)))
      | Tresult_param X => compare_ctor (Reduce (tag (Tresult_param X))) (fun _ => Reduce (data (Tresult_param X)))
      | Tresult_global on => compare_ctor (Reduce (tag (Tresult_global on))) (fun _ => Reduce (data (Tresult_global on)))
      | Tresult_unop op t => compare_ctor (Reduce (tag (Tresult_unop op t))) (fun _ => Reduce (data (Tresult_unop op t)))
      | Tresult_binop op tl tr => compare_ctor (Reduce (tag (Tresult_binop op tl tr))) (fun _ => Reduce (data (Tresult_binop op tl tr)))
      | Tresult_call on ts => compare_ctor (Reduce (tag (Tresult_call on ts))) (fun _ => Reduce (data (Tresult_call on ts)))
      | Tresult_member_call on t ts => compare_ctor (Reduce (tag (Tresult_member_call on t ts))) (fun _ => Reduce (data (Tresult_member_call on t ts)))
      | Tresult_parenlist t ts => compare_ctor (Reduce (tag (Tresult_parenlist t ts))) (fun _ => Reduce (data (Tresult_parenlist t ts)))
      | Tresult_member t f => compare_ctor (Reduce (tag (Tresult_member t f))) (fun _ => Reduce (data (Tresult_member t f)))
      | Tptr t => compare_ctor (Reduce (tag (Tptr t))) (fun _ => Reduce (data (Tptr t)))
      | Tref t => compare_ctor (Reduce (tag (Tref t))) (fun _ => Reduce (data (Tref t)))
      | Trv_ref t => compare_ctor (Reduce (tag (Trv_ref t))) (fun _ => Reduce (data (Trv_ref t)))
      | Tnum sz sgn => compare_ctor (Reduce (tag (Tnum sz sgn))) (fun _ => Reduce (data (Tnum sz sgn)))
      | Tchar_ t => compare_ctor (Reduce (tag (Tchar_ t))) (fun _ => Reduce (data (Tchar_ t)))
      | Tvoid => compare_tag (Reduce (tag Tvoid))
      | Tarray t n => compare_ctor (Reduce (tag (Tarray t n))) (fun _ => Reduce (data (Tarray t n)))
      | Tincomplete_array t => compare_ctor (Reduce (tag (Tincomplete_array t))) (fun _ => Reduce (data (Tincomplete_array t)))
      | Tvariable_array t e => compare_ctor (Reduce (tag (Tvariable_array t e))) (fun _ => Reduce (data (Tvariable_array t e)))
      | Tnamed gn => compare_ctor (Reduce (tag (Tnamed gn))) (fun _ => Reduce (data (Tnamed gn)))
      | Tenum gn => compare_ctor (Reduce (tag (Tenum gn))) (fun _ => Reduce (data (Tenum gn)))
      | Tfunction t => compare_ctor (Reduce (tag (Tfunction t))) (fun _ => Reduce (data (Tfunction t)))
      | Tbool => compare_tag (Reduce (tag Tbool))
      | Tmember_pointer gn t => compare_ctor (Reduce (tag (Tmember_pointer gn t))) (fun _ => Reduce (data (Tmember_pointer gn t)))
      | Tfloat_ t => compare_ctor (Reduce (tag (Tfloat_ t))) (fun _ => Reduce (data (Tfloat_ t)))
      | Tqualified cv t => compare_ctor (Reduce (tag (Tqualified cv t))) (fun _ => Reduce (data (Tqualified cv t)))
      | Tnullptr => compare_tag (Reduce (tag Tnullptr))
      | Tarch sz n => compare_ctor (Reduce (tag (Tarch sz n))) (fun _ => Reduce (data (Tarch sz n)))
      | Tdecltype e => compare_ctor (Reduce (tag (Tdecltype e))) (fun _ => Reduce (data (Tdecltype e)))
      | Tunsupported msg => compare_ctor (Reduce (tag (Tunsupported msg))) (fun _ => Reduce (data (Tunsupported msg)))
      end.
  End compare_body.
End type.

Module Expr.
  Section compare_body.
    Context {lang : lang.t}.
    #[local] Notation name := (name' lang).
    #[local] Notation type := (type' lang).
    #[local] Notation Expr := (Expr' lang).
    #[local] Notation Stmt := (Stmt' lang).
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    Context (compareS : Stmt -> Stmt -> comparison).

    Record box_Eunresolved_unop : Set := Box_Eunresolved_unop {
      box_Eunresolved_unop_0 : RUnOp;
      box_Eunresolved_unop_1 : Expr;
    }.
    Definition box_Eunresolved_unop_compare (b1 b2 : box_Eunresolved_unop) : comparison :=
      compare_lex (RUnOp.compare b1.(box_Eunresolved_unop_0) b2.(box_Eunresolved_unop_0)) $ fun _ =>
      compareE b1.(box_Eunresolved_unop_1) b2.(box_Eunresolved_unop_1).

    Record box_Eunresolved_binop : Set := Box_Eunresolved_binop {
      box_Eunresolved_binop_0 : RBinOp;
      box_Eunresolved_binop_1 : Expr;
      box_Eunresolved_binop_2 : Expr;
    }.
    Definition box_Eunresolved_binop_compare (b1 b2 : box_Eunresolved_binop) : comparison :=
      compare_lex (RBinOp.compare b1.(box_Eunresolved_binop_0) b2.(box_Eunresolved_binop_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eunresolved_binop_1) b2.(box_Eunresolved_binop_1)) $ fun _ =>
      compareE b1.(box_Eunresolved_binop_2) b2.(box_Eunresolved_binop_2).

    Record box_Eunresolved_call : Set := Box_Eunresolved_call {
      box_Eunresolved_call_0 : name;
      box_Eunresolved_call_1 : list Expr;
    }.
    Definition box_Eunresolved_call_compare (b1 b2 : box_Eunresolved_call) : comparison :=
      compare_lex (compareN b1.(box_Eunresolved_call_0) b2.(box_Eunresolved_call_0)) $ fun _ =>
      List.compare compareE b1.(box_Eunresolved_call_1) b2.(box_Eunresolved_call_1).

    Record box_Eunresolved_member_call : Set := Box_Eunresolved_member_call {
      box_Eunresolved_member_call_0 : name;
      box_Eunresolved_member_call_1 : Expr;
      box_Eunresolved_member_call_2 : list Expr;
    }.
    Definition box_Eunresolved_member_call_compare (b1 b2 : box_Eunresolved_member_call) : comparison :=
      compare_lex (compareN b1.(box_Eunresolved_member_call_0) b2.(box_Eunresolved_member_call_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eunresolved_member_call_1) b2.(box_Eunresolved_member_call_1)) $ fun _ =>
      List.compare compareE b1.(box_Eunresolved_member_call_2) b2.(box_Eunresolved_member_call_2).

    Record box_Eunresolved_parenlist : Set := Box_Eunresolved_parenlist {
      box_Eunresolved_parenlist_0 : option type;
      box_Eunresolved_parenlist_1 : list Expr;
    }.
    Definition box_Eunresolved_parenlist_compare (b1 b2 : box_Eunresolved_parenlist) : comparison :=
      compare_lex (option.compare compareT b1.(box_Eunresolved_parenlist_0) b2.(box_Eunresolved_parenlist_0)) $ fun _ =>
      List.compare compareE b1.(box_Eunresolved_parenlist_1) b2.(box_Eunresolved_parenlist_1).

    Record box_Eunresolved_member : Set := Box_Eunresolved_member {
      box_Eunresolved_member_0 : Expr;
      box_Eunresolved_member_1 : ident;
    }.
    Definition box_Eunresolved_member_compare (b1 b2 : box_Eunresolved_member) : comparison :=
      compare_lex (compareE b1.(box_Eunresolved_member_0) b2.(box_Eunresolved_member_0)) $ fun _ =>
      bs_cmp b1.(box_Eunresolved_member_1) b2.(box_Eunresolved_member_1).

    Record box_Evar : Set := Box_Evar {
      box_Evar_0 : localname;
      box_Evar_1 : type;
    }.
    Definition box_Evar_compare (b1 b2 : box_Evar) : comparison :=
      compare_lex (bs_cmp b1.(box_Evar_0) b2.(box_Evar_0)) $ fun _ =>
      compareT b1.(box_Evar_1) b2.(box_Evar_1).

    Record box_Eenum_const : Set := Box_Eenum_const {
      box_Eenum_const_0 : name;
      box_Eenum_const_1 : ident;
    }.
    Definition box_Eenum_const_compare (b1 b2 : box_Eenum_const) : comparison :=
      compare_lex (compareN b1.(box_Eenum_const_0) b2.(box_Eenum_const_0)) $ fun _ =>
      bs_cmp b1.(box_Eenum_const_1) b2.(box_Eenum_const_1).

    Record box_Eglobal : Set := Box_Eglobal {
      box_Eglobal_0 : name;
      box_Eglobal_1 : type;
    }.
    Definition box_Eglobal_compare (b1 b2 : box_Eglobal) : comparison :=
      compare_lex (compareN b1.(box_Eglobal_0) b2.(box_Eglobal_0)) $ fun _ =>
      compareT b1.(box_Eglobal_1) b2.(box_Eglobal_1).

    Record box_Echar : Set := Box_Echar {
      box_Echar_0 : N;
      box_Echar_1 : type;
    }.
    Definition box_Echar_compare (b1 b2 : box_Echar) : comparison :=
      compare_lex (N.compare b1.(box_Echar_0) b2.(box_Echar_0)) $ fun _ =>
      compareT b1.(box_Echar_1) b2.(box_Echar_1).

    Record box_Estring : Set := Box_Estring {
      box_Estring_0 : list N;
      box_Estring_1 : type;
    }.
    Definition box_Estring_compare (b1 b2 : box_Estring) : comparison :=
      compare_lex (List.compare N.compare b1.(box_Estring_0) b2.(box_Estring_0)) $ fun _ =>
      compareT b1.(box_Estring_1) b2.(box_Estring_1).

    Record box_Eint : Set := Box_Eint {
      box_Eint_0 : Z;
      box_Eint_1 : type;
    }.
    Definition box_Eint_compare (b1 b2 : box_Eint) : comparison :=
      compare_lex (Z.compare b1.(box_Eint_0) b2.(box_Eint_0)) $ fun _ =>
      compareT b1.(box_Eint_1) b2.(box_Eint_1).

    Record box_Eunop : Set := Box_Eunop {
      box_Eunop_0 : UnOp;
      box_Eunop_1 : Expr;
      box_Eunop_2 : type;
    }.
    Definition box_Eunop_compare (b1 b2 : box_Eunop) : comparison :=
      compare_lex (UnOp.compare b1.(box_Eunop_0) b2.(box_Eunop_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eunop_1) b2.(box_Eunop_1)) $ fun _ =>
      compareT b1.(box_Eunop_2) b2.(box_Eunop_2).

    Record box_Ebinop : Set := Box_Ebinop {
      box_Ebinop_0 : BinOp;
      box_Ebinop_1 : Expr;
      box_Ebinop_2 : Expr;
      box_Ebinop_3 : type;
    }.
    Definition box_Ebinop_compare (b1 b2 : box_Ebinop) : comparison :=
      compare_lex (BinOp.compare b1.(box_Ebinop_0) b2.(box_Ebinop_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Ebinop_1) b2.(box_Ebinop_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Ebinop_2) b2.(box_Ebinop_2)) $ fun _ =>
      compareT b1.(box_Ebinop_3) b2.(box_Ebinop_3).

    Record box_Ederef : Set := Box_Ederef {
      box_Ederef_0 : Expr;
      box_Ederef_1 : type;
    }.
    Definition box_Ederef_compare (b1 b2 : box_Ederef) : comparison :=
      compare_lex (compareE b1.(box_Ederef_0) b2.(box_Ederef_0)) $ fun _ =>
      compareT b1.(box_Ederef_1) b2.(box_Ederef_1).

    Record box_Eassign : Set := Box_Eassign {
      box_Eassign_0 : Expr;
      box_Eassign_1 : Expr;
      box_Eassign_2 : type;
    }.
    Definition box_Eassign_compare (b1 b2 : box_Eassign) : comparison :=
      compare_lex (compareE b1.(box_Eassign_0) b2.(box_Eassign_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eassign_1) b2.(box_Eassign_1)) $ fun _ =>
      compareT b1.(box_Eassign_2) b2.(box_Eassign_2).

    Record box_Eseqand : Set := Box_Eseqand {
      box_Eseqand_0 : Expr;
      box_Eseqand_1 : Expr;
    }.
    Definition box_Eseqand_compare (b1 b2 : box_Eseqand) : comparison :=
      compare_lex (compareE b1.(box_Eseqand_0) b2.(box_Eseqand_0)) $ fun _ =>
      compareE b1.(box_Eseqand_1) b2.(box_Eseqand_1).

    Record box_Ecall : Set := Box_Ecall {
      box_Ecall_0 : Expr;
      box_Ecall_1 : list Expr;
    }.
    Definition box_Ecall_compare (b1 b2 : box_Ecall) : comparison :=
      compare_lex (compareE b1.(box_Ecall_0) b2.(box_Ecall_0)) $ fun _ =>
      List.compare compareE b1.(box_Ecall_1) b2.(box_Ecall_1).

    Record box_Ecast : Set := Box_Ecast {
      box_Ecast_0 : Cast_ type name type;
      box_Ecast_1 : Expr;
      box_Ecast_2 : type;
    }.
    Definition box_Ecast_compare (b1 b2 : box_Ecast) : comparison :=
      compare_lex (Cast.compare compareT compareN compareT b1.(box_Ecast_0) b2.(box_Ecast_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Ecast_1) b2.(box_Ecast_1)) $ fun _ =>
      compareT b1.(box_Ecast_2) b2.(box_Ecast_2).

    Record box_Edependent_cast : Set := Box_Edependent_cast {
      box_Edependent_cast_0 : Expr ;
      box_Edependent_cast_1 : type;
    }.
    Definition box_Edependent_cast_compare (b1 b2 : box_Edependent_cast) : comparison :=
      compare_lex (compareE b1.(box_Edependent_cast_0) b2.(box_Edependent_cast_0)) $ fun _ =>
      compareT b1.(box_Edependent_cast_1) b2.(box_Edependent_cast_1).

    Record box_Emember : Set := Box_Emember {
      box_Emember_0 : bool ;
      box_Emember_1 : Expr;
      box_Emember_2 : ident;
      box_Emember_3 : bool;
      box_Emember_4 : type;
    }.
    Definition box_Emember_compare (b1 b2 : box_Emember) : comparison :=
      compare_lex (Bool.compare b1.(box_Emember_0) b2.(box_Emember_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Emember_1) b2.(box_Emember_1)) $ fun _ =>
      compare_lex (bs_cmp b1.(box_Emember_2) b2.(box_Emember_2)) $ fun _ =>
      compare_lex (Bool.compare b1.(box_Emember_3) b2.(box_Emember_3)) $ fun _ =>
      compareT b1.(box_Emember_4) b2.(box_Emember_4).

    Record box_Emember_call : Set := Box_Emember_call {
      box_Emember_call_0 : bool ;
      box_Emember_call_1 : MethodRef' lang;
      box_Emember_call_2 : Expr;
      box_Emember_call_3 : list Expr;
    }.
    Definition box_Emember_call_compare (b1 b2 : box_Emember_call) : comparison :=
      compare_lex (Bool.compare b1.(box_Emember_call_0) b2.(box_Emember_call_0)) $ fun _ =>
      compare_lex (MethodRef.compare compareN compareT compareE b1.(box_Emember_call_1) b2.(box_Emember_call_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Emember_call_2) b2.(box_Emember_call_2)) $ fun _ =>
      List.compare compareE b1.(box_Emember_call_3) b2.(box_Emember_call_3).

    Record box_Eoperator_call : Set := Box_Eoperator_call {
      box_Eoperator_call_0 : OverloadableOperator;
      box_Eoperator_call_1 : operator_impl.t name type;
      box_Eoperator_call_2 : list Expr;
    }.
    Definition box_Eoperator_call_compare (b1 b2 : box_Eoperator_call) : comparison :=
      compare_lex (OverloadableOperator.compare b1.(box_Eoperator_call_0) b2.(box_Eoperator_call_0)) $ fun _ =>
      compare_lex (operator_impl.compare compareN compareT b1.(box_Eoperator_call_1) b2.(box_Eoperator_call_1)) $ fun _ =>
      List.compare compareE b1.(box_Eoperator_call_2) b2.(box_Eoperator_call_2).

    Record box_Esizeof : Set := Box_Esizeof {
      box_Esizeof_0 : type + Expr;
      box_Esizeof_1 : type;
    }.
    Definition box_Esizeof_compare (b1 b2 : box_Esizeof) : comparison :=
      compare_lex (sum.compare compareT compareE b1.(box_Esizeof_0) b2.(box_Esizeof_0)) $ fun _ =>
      compareT b1.(box_Esizeof_1) b2.(box_Esizeof_1).

    Record box_Eoffsetof : Set := Box_Eoffsetof {
      box_Eoffsetof_0 : type;
      box_Eoffsetof_1 : ident;
      box_Eoffsetof_2 : type;
    }.
    Definition box_Eoffsetof_compare (b1 b2 : box_Eoffsetof) : comparison :=
      compare_lex (compareT b1.(box_Eoffsetof_0) b2.(box_Eoffsetof_0)) $ fun _ =>
      compare_lex (bs_cmp b1.(box_Eoffsetof_1) b2.(box_Eoffsetof_1)) $ fun _ =>
      compareT b1.(box_Eoffsetof_2) b2.(box_Eoffsetof_2).

    Record box_Econstructor : Set := Box_Econstructor {
      box_Econstructor_0 : name;
      box_Econstructor_1 : list Expr;
      box_Econstructor_2 : type;
    }.
    Definition box_Econstructor_compare (b1 b2 : box_Econstructor) : comparison :=
      compare_lex (compareN b1.(box_Econstructor_0) b2.(box_Econstructor_0)) $ fun _ =>
      compare_lex (List.compare compareE b1.(box_Econstructor_1) b2.(box_Econstructor_1)) $ fun _ =>
      compareT b1.(box_Econstructor_2) b2.(box_Econstructor_2).

    Record box_Eif : Set := Box_Eif {
      box_Eif_0 : Expr;
      box_Eif_1 : Expr;
      box_Eif_2 : Expr;
      box_Eif_3 : ValCat;
      box_Eif_4 : type;
    }.
    Definition box_Eif_compare (b1 b2 : box_Eif) : comparison :=
      compare_lex (compareE b1.(box_Eif_0) b2.(box_Eif_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif_1) b2.(box_Eif_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif_2) b2.(box_Eif_2)) $ fun _ =>
      compare_lex (ValCat.compare b1.(box_Eif_3) b2.(box_Eif_3)) $ fun _ =>
      compareT b1.(box_Eif_4) b2.(box_Eif_4).

    Record box_Eif2 : Set := Box_Eif2 {
      box_Eif2_0 : N;
      box_Eif2_1 : Expr;
      box_Eif2_2 : Expr;
      box_Eif2_3 : Expr;
      box_Eif2_4 : Expr;
      box_Eif2_5 : ValCat;
      box_Eif2_6 : type;
    }.
    Definition box_Eif2_compare (b1 b2 : box_Eif2) : comparison :=
      compare_lex (N.compare b1.(box_Eif2_0) b2.(box_Eif2_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_1) b2.(box_Eif2_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_2) b2.(box_Eif2_2)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_3) b2.(box_Eif2_3)) $ fun _ =>
      compare_lex (compareE b1.(box_Eif2_4) b2.(box_Eif2_4)) $ fun _ =>
      compare_lex (ValCat.compare b1.(box_Eif2_5) b2.(box_Eif2_5)) $ fun _ =>
      compareT b1.(box_Eif2_6) b2.(box_Eif2_6).

    Record box_Einitlist : Set := Box_Einitlist {
      box_Einitlist_0 : list Expr;
      box_Einitlist_1 : option Expr;
      box_Einitlist_2 : type;
    }.
    Definition box_Einitlist_compare (b1 b2 : box_Einitlist) : comparison :=
      compare_lex (List.compare compareE b1.(box_Einitlist_0) b2.(box_Einitlist_0)) $ fun _ =>
      compare_lex (option.compare compareE b1.(box_Einitlist_1) b2.(box_Einitlist_1)) $ fun _ =>
      compareT b1.(box_Einitlist_2) b2.(box_Einitlist_2).

    Record box_Enew : Set := Box_Enew {
      box_Enew_0 : name * type;
      box_Enew_1 : list Expr;
      box_Enew_2 : new_form;
      box_Enew_3 : type;
      box_Enew_4 : option Expr;
      box_Enew_5 : option Expr;
    }.
    Definition box_Enew_compare (b1 b2 : box_Enew) : comparison :=
      compare_lex (prod.compare compareN compareT b1.(box_Enew_0) b2.(box_Enew_0)) $ fun _ =>
      compare_lex (List.compare compareE b1.(box_Enew_1) b2.(box_Enew_1)) $ fun _ =>
      compare_lex (new_form.compare b1.(box_Enew_2) b2.(box_Enew_2)) $ fun _ =>
      compare_lex (compareT b1.(box_Enew_3) b2.(box_Enew_3)) $ fun _ =>
      compare_lex (option.compare compareE b1.(box_Enew_4) b2.(box_Enew_4)) $ fun _ =>
      option.compare compareE b1.(box_Enew_5) b2.(box_Enew_5).

    Record box_Edelete : Set := Box_Edelete {
      box_Edelete_0 : bool;
      box_Edelete_1 : name * type;
      box_Edelete_2 : Expr;
      box_Edelete_3 : type;
    }.
    Definition box_Edelete_compare (b1 b2 : box_Edelete) : comparison :=
      compare_lex (Bool.compare b1.(box_Edelete_0) b2.(box_Edelete_0)) $ fun _ =>
      compare_lex (prod.compare compareN compareT b1.(box_Edelete_1) b2.(box_Edelete_1)) $ fun _ =>
      compare_lex (compareE b1.(box_Edelete_2) b2.(box_Edelete_2)) $ fun _ =>
      compareT b1.(box_Edelete_3) b2.(box_Edelete_3).

    Record box_Ematerialize_temp : Set := Box_Ematerialize_temp {
      box_Ematerialize_temp_0 : Expr;
      box_Ematerialize_temp_1 : ValCat;
    }.
    Definition box_Ematerialize_temp_compare (b1 b2 : box_Ematerialize_temp) : comparison :=
      compare_lex (compareE b1.(box_Ematerialize_temp_0) b2.(box_Ematerialize_temp_0)) $ fun _ =>
      ValCat.compare b1.(box_Ematerialize_temp_1) b2.(box_Ematerialize_temp_1).

    Record box_Eatomic : Set := Box_Eatomic {
      box_Eatomic_0 : AtomicOp;
      box_Eatomic_1 : list Expr;
      box_Eatomic_2 : type;
    }.
    Definition box_Eatomic_compare (b1 b2 : box_Eatomic) : comparison :=
      compare_lex (AtomicOp.compare b1.(box_Eatomic_0) b2.(box_Eatomic_0)) $ fun _ =>
      compare_lex (List.compare compareE b1.(box_Eatomic_1) b2.(box_Eatomic_1)) $ fun _ =>
      compareT b1.(box_Eatomic_2) b2.(box_Eatomic_2).

    Record box_Epseudo_destructor : Set := Box_Epseudo_destructor {
      box_Epseudo_destructor_0 : bool;
      box_Epseudo_destructor_1 : type;
      box_Epseudo_destructor_2 : Expr;
    }.
    Definition box_Epseudo_destructor_compare (b1 b2 : box_Epseudo_destructor) : comparison :=
      compare_lex (Bool.compare b1.(box_Epseudo_destructor_0) b2.(box_Epseudo_destructor_0)) $ fun _ =>
      compare_lex (compareT b1.(box_Epseudo_destructor_1) b2.(box_Epseudo_destructor_1)) $ fun _ =>
      compareE b1.(box_Epseudo_destructor_2) b2.(box_Epseudo_destructor_2).

    Record box_Earrayloop_init : Set := Box_Earrayloop_init {
      box_Earrayloop_init_0 : N;
      box_Earrayloop_init_1 : Expr;
      box_Earrayloop_init_2 : N;
      box_Earrayloop_init_3 : N;
      box_Earrayloop_init_4 : Expr;
      box_Earrayloop_init_5 : type;
    }.
    Definition box_Earrayloop_init_compare (b1 b2 : box_Earrayloop_init) : comparison :=
      compare_lex (N.compare b1.(box_Earrayloop_init_0) b2.(box_Earrayloop_init_0)) $ fun _ =>
      compare_lex (compareE b1.(box_Earrayloop_init_1) b2.(box_Earrayloop_init_1)) $ fun _ =>
      compare_lex (N.compare b1.(box_Earrayloop_init_2) b2.(box_Earrayloop_init_2)) $ fun _ =>
      compare_lex (N.compare b1.(box_Earrayloop_init_3) b2.(box_Earrayloop_init_3)) $ fun _ =>
      compare_lex (compareE b1.(box_Earrayloop_init_4) b2.(box_Earrayloop_init_4)) $ fun _ =>
      compareT b1.(box_Earrayloop_init_5) b2.(box_Earrayloop_init_5).

    Record box_Eopaque_ref : Set := Box_Eopaque_ref {
      box_Eopaque_ref_0 : N;
      box_Eopaque_ref_1 : ValCat;
      box_Eopaque_ref_2 : type;
    }.
    Definition box_Eopaque_ref_compare (b1 b2 : box_Eopaque_ref) : comparison :=
      compare_lex (N.compare b1.(box_Eopaque_ref_0) b2.(box_Eopaque_ref_0)) $ fun _ =>
      compare_lex (ValCat.compare b1.(box_Eopaque_ref_1) b2.(box_Eopaque_ref_1)) $ fun _ =>
      compareT b1.(box_Eopaque_ref_2) b2.(box_Eopaque_ref_2).

    Record box_Eunsupported : Set := Box_Eunsupported {
      box_Eunsupported_0 : bs;
      box_Eunsupported_1 : ValCat;
      box_Eunsupported_2 : type;
    }.
    Definition box_Eunsupported_compare (b1 b2 : box_Eunsupported) : comparison :=
      compare_lex (bs_cmp b1.(box_Eunsupported_0) b2.(box_Eunsupported_0)) $ fun _ =>
      compare_lex (ValCat.compare b1.(box_Eunsupported_1) b2.(box_Eunsupported_1)) $ fun _ =>
      compareT b1.(box_Eunsupported_2) b2.(box_Eunsupported_2).

    Record box_Estmt : Set := Box_Estmt {
      box_Estmt_0 : Stmt;
      box_Estmt_1 : type
    }.
    Definition box_Estmt_compare (b1 b2 : box_Estmt) : comparison :=
      compare_lex (compareS b1.(box_Estmt_0) b2.(box_Estmt_0)) $ fun _ =>
      compareT b1.(box_Estmt_1) b2.(box_Estmt_1).

    Definition tag (e : Expr) : positive :=
      match e with
      | Eparam _ => 1
      | Eunresolved_global _ => 2
      | Eunresolved_unop _ _ => 3
      | Eunresolved_binop _ _ _ => 4
      | Eunresolved_call _ _ => 5
      | Eunresolved_member_call _ _ _ => 6
      | Eunresolved_parenlist _ _ => 7
      | Eunresolved_member _ _ => 8
      | Edependent_cast _ _ => 59
      | Evar _ _ => 9
      | Eenum_const _ _ => 10
      | Eglobal _ _ => 11
      | Echar _ _ => 12
      | Estring _ _ => 13
      | Eint _ _ => 14
      | Ebool _ => 15
      | Eunop _ _ _ => 16
      | Ebinop _ _ _ _ => 17
      | Ederef _ _ => 18
      | Eaddrof _ => 19
      | Eassign _ _ _ => 20
      | Eassign_op _ _ _ _ => 21
      | Epreinc _ _ => 22
      | Epostinc _ _ => 23
      | Epredec _ _ => 24
      | Epostdec _ _ => 25
      | Eseqand _ _ => 26
      | Eseqor _ _ => 27
      | Ecomma _ _ => 28
      | Ecall _ _ => 29
      | Ecast _ _ _ => 30
      | Emember _ _ _ _ _ => 31
      | Emember_call _ _ _ _ => 32
      | Eoperator_call _ _ _ => 33
      | Esubscript _ _ _ => 34
      | Esizeof _ _ => 35
      | Ealignof _ _ => 36
      | Eoffsetof _ _ _ => 37
      | Econstructor _ _ _ => 38
      | Eimplicit _ => 39
      | Eimplicit_init _ => 40
      | Eif _ _ _ _ _ => 41
      | Eif2 _ _ _ _ _ _ _ => 42
      | Ethis _ => 43
      | Enull => 44
      | Einitlist _ _ _ => 45
      | Enew _ _ _ _ _ _ => 46
      | Edelete _ _ _ _ => 47
      | Eandclean _ => 48
      | Ematerialize_temp _ _ => 49
      | Eatomic _ _ _ => 50
      | Eva_arg _ _ => 51
      | Epseudo_destructor _ _ _ => 52
      | Earrayloop_init _ _ _ _ _ _ => 53
      | Earrayloop_index _ _ => 54
      | Eopaque_ref _ _ _ => 55
      | Eglobal_member _ _ => 56
      | Eunsupported _ _ _ => 57
      | Estmt _ _ => 58
      end.
    Definition car (t : positive) : Set :=
      match t with
      | 1 => ident
      | 2 => name
      | 3 => box_Eunresolved_unop
      | 4 => box_Eunresolved_binop
      | 5 => box_Eunresolved_call
      | 6 => box_Eunresolved_member_call
      | 7 => box_Eunresolved_parenlist
      | 8 => box_Eunresolved_member
      | 9 => box_Evar
      | 10 => box_Eenum_const
      | 11 => box_Eglobal
      | 12 => box_Echar
      | 13 => box_Estring
      | 14 => box_Eint
      | 15 => bool
      | 16 => box_Eunop
      | 17 => box_Ebinop
      | 18 => box_Ederef
      | 19 => Expr
      | 20 => box_Eassign
      | 21 => box_Ebinop
      | 22 | 23 | 24 | 25 => box_Ederef
      | 26 | 27 | 28 => box_Eseqand
      | 29 => box_Ecall
      | 30 => box_Ecast
      | 31 => box_Emember
      | 32 => box_Emember_call
      | 33 => box_Eoperator_call
      | 34 => box_Eassign
      | 35 | 36 => box_Esizeof
      | 37 => box_Eoffsetof
      | 38 => box_Econstructor
      | 39 => Expr
      | 40 => type
      | 41 => box_Eif
      | 42 => box_Eif2
      | 43 => type
      | 44 => unit
      | 45 => box_Einitlist
      | 46 => box_Enew
      | 47 => box_Edelete
      | 48 => Expr
      | 49 => box_Ematerialize_temp
      | 50 => box_Eatomic
      | 51 => box_Ederef
      | 52 => box_Epseudo_destructor
      | 53 => box_Earrayloop_init
      | 54 => box_Echar
      | 55 => box_Eopaque_ref
      | 56 => box_Eglobal
      | 58 => box_Estmt
      | 59 => box_Edependent_cast
      | _ => box_Eunsupported
      end.
    Definition data (e : Expr) : car (tag e) :=
      match e with
      | Eparam X => X
      | Eunresolved_global on => on
      | Eunresolved_unop op e => Box_Eunresolved_unop op e
      | Eunresolved_binop op l r => Box_Eunresolved_binop op l r
      | Eunresolved_call on es => Box_Eunresolved_call on es
      | Eunresolved_member_call on e es => Box_Eunresolved_member_call on e es
      | Eunresolved_parenlist e es => Box_Eunresolved_parenlist e es
      | Eunresolved_member e f => Box_Eunresolved_member e f
      | Edependent_cast e t => Box_Edependent_cast e t
      | Evar n t => Box_Evar n t
      | Eenum_const gn id => Box_Eenum_const gn id
      | Eglobal on t => Box_Eglobal on t
      | Eglobal_member on t => Box_Eglobal on t
      | Echar c t => Box_Echar c t
      | Estring s t => Box_Estring s t
      | Eint n t => Box_Eint n t
      | Ebool b => b
      | Eunop op e t => Box_Eunop op e t
      | Ebinop op l r t => Box_Ebinop op l r t
      | Ederef e t => Box_Ederef e t
      | Eaddrof e => e
      | Eassign l r t => Box_Eassign l r t
      | Eassign_op op l r t => Box_Ebinop op l r t
      | Epreinc e t
      | Epostinc e t
      | Epredec e t
      | Epostdec e t => Box_Ederef e t
      | Eseqand l r
      | Eseqor l r
      | Ecomma l r => Box_Eseqand l r
      | Ecall e es => Box_Ecall e es
      | Ecast c e t => Box_Ecast c e t
      | Emember arrow e x b t => Box_Emember arrow e x b t
      | Emember_call arrow m e es => Box_Emember_call arrow m e es
      | Eoperator_call oo oi es => Box_Eoperator_call oo oi es
      | Esubscript l r t => Box_Eassign l r t
      | Esizeof a t
      | Ealignof a t => Box_Esizeof a t
      | Eoffsetof cls m t => Box_Eoffsetof cls m t
      | Econstructor cls es t => Box_Econstructor cls es t
      | Eimplicit e => e
      | Eimplicit_init t => t
      | Eif c l r vc t => Box_Eif c l r vc t
      | Eif2 n s c l r vc t => Box_Eif2 n s c l r vc t
      | Ethis t => t
      | Enull => ()
      | Einitlist es i t => Box_Einitlist es i t
      | Enew fn es a ty sz i => Box_Enew fn es a ty sz i
      | Edelete a fn e t => Box_Edelete a fn e t
      | Eandclean e => e
      | Ematerialize_temp e vc => Box_Ematerialize_temp e vc
      | Eatomic op es t => Box_Eatomic op es t
      | Estmt s t => Box_Estmt s t
      | Eva_arg e t => Box_Ederef e t
      | Epseudo_destructor a t e => Box_Epseudo_destructor a t e
      | Earrayloop_init on s lev len i t => Box_Earrayloop_init on s lev len i t
      | Earrayloop_index c t => Box_Echar c t
      | Eopaque_ref n vc t => Box_Eopaque_ref n vc t
      | Eunsupported msg vc t => Box_Eunsupported msg vc t
      end.
    Definition compare_data (t : positive) : car t -> car t -> comparison :=
      match t with
      | 1 => bs_cmp
      | 2 => compareN
      | 3 => box_Eunresolved_unop_compare
      | 4 => box_Eunresolved_binop_compare
      | 5 => box_Eunresolved_call_compare
      | 6 => box_Eunresolved_member_call_compare
      | 7 => box_Eunresolved_parenlist_compare
      | 8 => box_Eunresolved_member_compare
      | 9 => box_Evar_compare
      | 10 => box_Eenum_const_compare
      | 11 => box_Eglobal_compare
      | 12 => box_Echar_compare
      | 13 => box_Estring_compare
      | 14 => box_Eint_compare
      | 15 => Bool.compare
      | 16 => box_Eunop_compare
      | 17 => box_Ebinop_compare
      | 18 => box_Ederef_compare
      | 19 => compareE
      | 20 => box_Eassign_compare
      | 21 => box_Ebinop_compare
      | 22 | 23 | 24 | 25 => box_Ederef_compare
      | 26 | 27 | 28 => box_Eseqand_compare
      | 29 => box_Ecall_compare
      | 30 => box_Ecast_compare
      | 31 => box_Emember_compare
      | 32 => box_Emember_call_compare
      | 33 => box_Eoperator_call_compare
      | 34 => box_Eassign_compare
      | 35 | 36 => box_Esizeof_compare
      | 37 => box_Eoffsetof_compare
      | 38 => box_Econstructor_compare
      | 39 => compareE
      | 40 => compareT
      | 41 => box_Eif_compare
      | 42 => box_Eif2_compare
      | 43 => compareT
      | 44 => fun _ _ => Eq
      | 45 => box_Einitlist_compare
      | 46 => box_Enew_compare
      | 47 => box_Edelete_compare
      | 48 => compareE
      | 49 => box_Ematerialize_temp_compare
      | 50 => box_Eatomic_compare
      | 51 => box_Ederef_compare
      | 52 => box_Epseudo_destructor_compare
      | 53 => box_Earrayloop_init_compare
      | 54 => box_Echar_compare
      | 55 => box_Eopaque_ref_compare
      | 56 => box_Eglobal_compare
      | 58 => box_Estmt_compare
      | 59 => box_Edependent_cast_compare
      | _ => box_Eunsupported_compare
      end.

    #[local] Notation compare_ctor := (compare_ctor tag car data compare_data).
    #[local] Notation compare_tag := (compare_tag tag).

    #[local] Notation COMP e := (compare_ctor (Reduce (tag e)) (fun _ => Reduce (data e))) (only parsing).

    Definition compare_body (e : Expr) : Expr -> comparison :=
      match e with
      | Eparam X => compare_ctor (Reduce (tag (Eparam X))) (fun _ => Reduce (data (Eparam X)))
      | Eunresolved_global on => compare_ctor (Reduce (tag (Eunresolved_global on))) (fun _ => Reduce (data (Eunresolved_global on)))
      | Eunresolved_unop op e => compare_ctor (Reduce (tag (Eunresolved_unop op e))) (fun _ => Reduce (data (Eunresolved_unop op e)))
      | Eunresolved_binop op l r => compare_ctor (Reduce (tag (Eunresolved_binop op l r))) (fun _ => Reduce (data (Eunresolved_binop op l r)))

      | Eunresolved_call on es => compare_ctor (Reduce (tag (Eunresolved_call on es))) (fun _ => Reduce (data (Eunresolved_call on es)))
      | Eunresolved_member_call on e es => compare_ctor (Reduce (tag (Eunresolved_member_call on e es))) (fun _ => Reduce (data (Eunresolved_member_call on e es)))
      | Eunresolved_parenlist e es => compare_ctor (Reduce (tag (Eunresolved_parenlist e es))) (fun _ => Reduce (data (Eunresolved_parenlist e es)))
      | Eunresolved_member e f => compare_ctor (Reduce (tag (Eunresolved_member e f))) (fun _ => Reduce (data (Eunresolved_member e f)))
      | Edependent_cast e t => COMP (Edependent_cast e t)

      | Evar n t => compare_ctor (Reduce (tag (Evar n t))) (fun _ => Reduce (data (Evar n t)))

      | Eenum_const gn id => compare_ctor (Reduce (tag (Eenum_const gn id))) (fun _ => Reduce (data (Eenum_const gn id)))
      | Eglobal on t => compare_ctor (Reduce (tag (Eglobal on t))) (fun _ => Reduce (data (Eglobal on t)))
      | Eglobal_member on t => compare_ctor (Reduce (tag (Eglobal_member on t))) (fun _ => Reduce (data (Eglobal_member on t)))

      | Echar c t => compare_ctor (Reduce (tag (Echar c t))) (fun _ => Reduce (data (Echar c t)))
      | Estring s t => compare_ctor (Reduce (tag (Estring s t))) (fun _ => Reduce (data (Estring s t)))
      | Eint n t => compare_ctor (Reduce (tag (Eint n t))) (fun _ => Reduce (data (Eint n t)))

      | Ebool b => compare_ctor (Reduce (tag (Ebool b))) (fun _ => Reduce (data (Ebool b)))
      | Eunop op e t => compare_ctor (Reduce (tag (Eunop op e t))) (fun _ => Reduce (data (Eunop op e t)))
      | Ebinop op l r t => compare_ctor (Reduce (tag (Ebinop op l r t))) (fun _ => Reduce (data (Ebinop op l r t)))
      | Ederef e t => compare_ctor (Reduce (tag (Ederef e t))) (fun _ => Reduce (data (Ederef e t)))
      | Eaddrof e => compare_ctor (Reduce (tag (Eaddrof e))) (fun _ => Reduce (data (Eaddrof e)))

      | Eassign l r t => compare_ctor (Reduce (tag (Eassign l r t))) (fun _ => Reduce (data (Eassign l r t)))
      | Eassign_op op l r t => compare_ctor (Reduce (tag (Eassign_op op l r t))) (fun _ => Reduce (data (Eassign_op op l r t)))
      | Epreinc e t => compare_ctor (Reduce (tag (Epreinc e t))) (fun _ => Reduce (data (Epreinc e t)))
      | Epostinc e t => compare_ctor (Reduce (tag (Epostinc e t))) (fun _ => Reduce (data (Epostinc e t)))
      | Epredec e t => compare_ctor (Reduce (tag (Epredec e t))) (fun _ => Reduce (data (Epredec e t)))

      | Epostdec e t => compare_ctor (Reduce (tag (Epostdec e t))) (fun _ => Reduce (data (Epostdec e t)))
      | Eseqand l r => compare_ctor (Reduce (tag (Eseqand l r))) (fun _ => Reduce (data (Eseqand l r)))
      | Eseqor l r => compare_ctor (Reduce (tag (Eseqor l r))) (fun _ => Reduce (data (Eseqor l r)))
      | Ecomma l r => compare_ctor (Reduce (tag (Ecomma l r))) (fun _ => Reduce (data (Ecomma l r)))
      | Ecall e es => compare_ctor (Reduce (tag (Ecall e es))) (fun _ => Reduce (data (Ecall e es)))

      | Ecast c e t => compare_ctor (Reduce (tag (Ecast c e t))) (fun _ => Reduce (data (Ecast c e t)))
      | Emember arr e x b t => compare_ctor (Reduce (tag (Emember arr e x b t))) (fun _ => Reduce (data (Emember arr e x b t)))
      | Emember_call arr m e es => compare_ctor (Reduce (tag (Emember_call arr m e es))) (fun _ => Reduce (data (Emember_call arr m e es)))
      | Eoperator_call oo oi es => compare_ctor (Reduce (tag (Eoperator_call oo oi es))) (fun _ => Reduce (data (Eoperator_call oo oi es)))
      | Esubscript l r t => compare_ctor (Reduce (tag (Esubscript l r t))) (fun _ => Reduce (data (Esubscript l r t)))

      | Esizeof a t => compare_ctor (Reduce (tag (Esizeof a t))) (fun _ => Reduce (data (Esizeof a t)))
      | Ealignof a t => compare_ctor (Reduce (tag (Ealignof a t))) (fun _ => Reduce (data (Ealignof a t)))
      | Eoffsetof cls m t => compare_ctor (Reduce (tag (Eoffsetof cls m t))) (fun _ => Reduce (data (Eoffsetof cls m t)))
      | Econstructor cls es t => compare_ctor (Reduce (tag (Econstructor cls es t))) (fun _ => Reduce (data (Econstructor cls es t)))
      | Eimplicit e => compare_ctor (Reduce (tag (Eimplicit e))) (fun _ => Reduce (data (Eimplicit e)))

      | Eimplicit_init t => compare_ctor (Reduce (tag (Eimplicit_init t))) (fun _ => Reduce (data (Eimplicit_init t)))
      | Eif c l r vc t => compare_ctor (Reduce (tag (Eif c l r vc t))) (fun _ => Reduce (data (Eif c l r vc t)))
      | Eif2 n s c l r vc t => compare_ctor (Reduce (tag (Eif2 n s c l r vc t))) (fun _ => Reduce (data (Eif2 n s c l r vc t)))
      | Ethis t => compare_ctor (Reduce (tag (Ethis t))) (fun _ => Reduce (data (Ethis t)))
      | Enull => compare_tag (Reduce (tag Enull))

      | Einitlist es i t => compare_ctor (Reduce (tag (Einitlist es i t))) (fun _ => Reduce (data (Einitlist es i t)))
      | Enew fn es a ty sz i => compare_ctor (Reduce (tag (Enew fn es a ty sz i))) (fun _ => Reduce (data (Enew fn es a ty sz i)))
      | Edelete a fn e t => compare_ctor (Reduce (tag (Edelete a fn e t))) (fun _ => Reduce (data (Edelete a fn e t)))
      | Eandclean e => compare_ctor (Reduce (tag (Eandclean e))) (fun _ => Reduce (data (Eandclean e)))
      | Ematerialize_temp e vc => compare_ctor (Reduce (tag (Ematerialize_temp e vc))) (fun _ => Reduce (data (Ematerialize_temp e vc)))

      | Eatomic op es t => compare_ctor (Reduce (tag (Eatomic op es t))) (fun _ => Reduce (data (Eatomic op es t)))
      | Eva_arg e t => compare_ctor (Reduce (tag (Eva_arg e t))) (fun _ => Reduce (data (Eva_arg e t)))
      | Epseudo_destructor a t e => compare_ctor (Reduce (tag (Epseudo_destructor a t e))) (fun _ => Reduce (data (Epseudo_destructor a t e)))
      | Earrayloop_init on s lev len i t => compare_ctor (Reduce (tag (Earrayloop_init on s lev len i t))) (fun _ => Reduce (data (Earrayloop_init on s lev len i t)))
      | Earrayloop_index c t => compare_ctor (Reduce (tag (Earrayloop_index c t))) (fun _ => Reduce (data (Earrayloop_index c t)))

      | Eopaque_ref n vc t => compare_ctor (Reduce (tag (Eopaque_ref n vc t))) (fun _ => Reduce (data (Eopaque_ref n vc t)))
      | Eunsupported msg vc t => compare_ctor (Reduce (tag (Eunsupported msg vc t))) (fun _ => Reduce (data (Eunsupported msg vc t)))
      | Estmt s t => compare_ctor (Reduce (tag $ Estmt s t)) (fun _ => Reduce (data $ Estmt s t))
      end.
  End compare_body.
End Expr.

  Structure comparator :=
    { _car : Set
    ; #[canonical=no] compare : _car -> _car -> comparison
    }.
  Arguments compare {_} _ _.
  Canonical unit_comparator :=
    {| _car := unit
    ; compare := fun _ _ => Eq |}.

  Canonical pair_comparator (C1 C2 : comparator) :=
    {| _car := C1.(_car) * C2.(_car)
    ; compare := fun '(a,b) '(c,d) => compare_lex (C1.(compare) a c) $ fun _ => C2.(compare) b d |}.
  Canonical option_comparator (C1 : comparator) :=
    {| _car := option C1.(_car)
    ; compare := option.compare C1.(compare) |}.
  Canonical list_comparator (C1 : comparator) :=
    {| _car := list C1.(_car)
    ; compare := List.compare C1.(compare) |}.
  Canonical bs_comparator :=
    {| _car := bs
    ; compare := bs_compare |}.
  Canonical localname_comparator :=
    {| _car := localname
     ; compare := bs_compare |}.
  Canonical ident_comparator :=
    {| _car := ident
    ; compare := bs_compare |}.
  Canonical bool_comparator :=
    {| _car := bool
    ; compare := Bool.compare |}.
  Definition SwitchBranch_compare (a b : SwitchBranch) : comparison :=
    match a , b with
    | Exact a , Exact b => Z.compare a b
    | Exact _ , Range _ _ => Lt
    | Range _ _ , Exact _ => Gt
    | Range a b , Range c d => compare_lex (Z.compare a c) $ fun _ => Z.compare b d
    end.
  #[local] Canonical SwitchBranch_comparator :=
    {| _car := SwitchBranch
    ; compare := SwitchBranch_compare |}.


Module VarDecl.
  Section compare_body.
    Context {lang : lang.t}.
    #[local] Notation name := (name' lang).
    #[local] Notation type := (type' lang).
    #[local] Notation Expr := (Expr' lang).
    #[local] Notation VarDecl := (VarDecl' lang).
    #[local] Notation Stmt := (Stmt' lang).
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    Context (compareVD : VarDecl -> VarDecl -> comparison).
    Context (compareS : Stmt -> Stmt -> comparison).

    #[local] Canonical name_comparator :=
      {| _car := name
      ; compare := compareN |}.
    #[local] Canonical type_comparator :=
      {| _car := type
       ; compare := compareT |}.
    #[local] Canonical expr_comparator :=
      {| _car := Expr
      ; compare := compareE |}.
    #[local] Canonical VarDecl_comparator :=
      {| _car := VarDecl
      ; compare := compareVD |}.

    Definition tag (vd : VarDecl) : positive :=
      match vd with
      | Dvar _ _ _ => 1
      | Ddecompose _ _ _ => 2
      | Dinit _ _ _ _ => 3
      end.
    Definition car (vd : positive) : Set :=
      match vd return Set with
      | 1 => localname * type * option Expr
      | 2 => Expr * ident * list VarDecl
      | _ => bool * name * type * option Expr
      end%type.
    Definition data (vd : VarDecl) : car (tag vd) :=
      match vd with
      | Dvar a b c => (a, b, c)
      | Ddecompose a b c => (a, b, c)
      | Dinit a b c d => (a, b, c, d)
      end.
    Definition compare_data (k : positive) : car k -> car k -> comparison :=
      match k as k return car k -> car k -> comparison with
      | 1 => compare
      | 2 => compare
      | _ => compare
      end.

    #[local] Notation compare_ctor X := (compare_ctor tag car data compare_data (Reduce (tag X)) (fun _ => Reduce (data X))) (only parsing).
    Definition compare_body (vd : VarDecl) : VarDecl -> comparison :=
      match vd with
      | Dvar a b c => compare_ctor (Dvar a b c)
      | Ddecompose a b c => compare_ctor (Ddecompose a b c)
      | Dinit a b c d => compare_ctor (Dinit a b c d)
      end.
  End compare_body.
End VarDecl.

Module Stmt.
  Section compare_body.
    Context {lang : lang.t}.
    #[local] Notation name := (name' lang).
    #[local] Notation type := (type' lang).
    #[local] Notation Expr := (Expr' lang).
    #[local] Notation VarDecl := (VarDecl' lang).
    #[local] Notation Stmt := (Stmt' lang).
    Context (compareN : name -> name -> comparison).
    Context (compareT : type -> type -> comparison).
    Context (compareE : Expr -> Expr -> comparison).
    Context (compareVD : VarDecl -> VarDecl -> comparison).
    Context (compareS : Stmt -> Stmt -> comparison).

    #[local] Canonical name_comparator :=
      {| _car := name
      ; compare := compareN |}.
    #[local] Canonical type_comparator :=
      {| _car := type
       ; compare := compareT |}.
    #[local] Canonical expr_comparator :=
      {| _car := Expr
      ; compare := compareE |}.
    #[local] Canonical VarDecl_comparator :=
      {| _car := VarDecl
      ; compare := compareVD |}.
    #[local] Canonical Stmt_comparator :=
      {| _car := _
      ; compare := compareS |}.

    Definition tag (s : Stmt) : positive :=
      match s with
      | Sseq _ => 1
      | Sdecl _ => 2
      | Sif _ _ _ _ => 3
      | Swhile _ _ _ => 4
      | Sfor _ _ _ _ => 5
      | Sdo _ _ => 6
      | Sswitch _ _ _ => 7
      | Scase _ => 8
      | Sdefault => 9
      | Sbreak => 10
      | Scontinue => 11
      | Sreturn _ => 12
      | Sexpr _ => 13
      | Sattr _ _ => 14
      | Sasm _ _ _ _ _ => 15
      | Slabeled _ _ => 16
      | Sgoto _ => 17
      | Sunsupported _ => 18
      end.
    Definition car (k : positive) : Set :=
      match k with
      | 1 => list Stmt
      | 2 => list VarDecl
      | 3 => option VarDecl * Expr * Stmt * Stmt
      | 4 => option VarDecl * Expr * Stmt
      | 5 => option Stmt * option Expr * option Expr * Stmt
      | 6 => Stmt * Expr
      | 7 => option VarDecl * Expr * Stmt
      | 8 => SwitchBranch
      | 9 => unit
      | 10 => unit
      | 11 => unit
      | 12 => option Expr
      | 13 => Expr
      | 14 => list ident * Stmt
      | 15 => bs * bool * list (ident * Expr) * list (ident * Expr) * list ident
      | 16 => ident * Stmt
      | 17 => ident
      | _ => bs
      end.
    Definition data (s : Stmt) : car (tag s) :=
      match s with
      | Sseq a => a
      | Sdecl a => a
      | Sif a b c d => (a,b,c,d)
      | Swhile a b c => (a,b,c)
      | Sfor a b c d => (a,b,c,d)
      | Sdo a b => (a,b)
      | Sswitch a b c => (a,b,c)
      | Scase a => a
      | Sdefault => tt
      | Sbreak => ()
      | Scontinue => ()
      | Sreturn a => a
      | Sexpr a => a
      | Sattr a b => (a,b)
      | Sasm a b c d e => (a,b,c,d,e)
      | Slabeled a b => (a,b)
      | Sgoto a => a
      | Sunsupported a => a
      end.

    Definition compare_data  (k : positive) : car k -> car k -> comparison :=
      match k as k return car k -> car k -> comparison with
      | 1 => compare
      | 2 => compare
      | 3 => compare
      | 4 => compare
      | 5 => compare
      | 6 => compare
      | 7 => compare
      | 8 => compare
      | 9 => compare
      | 10 => compare
      | 11 => compare
      | 12 => compare
      | 13 => compare
      | 14 => compare
      | 15 => compare
      | 16 => compare
      | 17 => compare
      | _ => compare
      end.

    #[local] Notation compare_ctor X := (compare_ctor tag car data compare_data (Reduce (tag X)) (fun _ => Reduce (data X))) (only parsing).
    Definition compare_body (s : Stmt) : Stmt -> comparison :=
      match s with
      | Sseq a => compare_ctor (Sseq a)
      | Sdecl a => compare_ctor (Sdecl a)
      | Sif a b c d => compare_ctor (Sif a b c d)
      | Swhile a b c => compare_ctor (Swhile a b c)
      | Sfor a b c d => compare_ctor (Sfor a b c d)
      | Sdo a b => compare_ctor (Sdo a b)
      | Sswitch a b c => compare_ctor (Sswitch a b c)
      | Scase a => compare_ctor (Scase (lang:=lang) a)
      | Sdefault => compare_ctor (Sdefault (lang:=lang))
      | Sbreak => compare_ctor (Sbreak (lang:=lang))
      | Scontinue => compare_ctor (Scontinue (lang:=lang))
      | Sreturn a => compare_ctor (Sreturn a)
      | Sexpr a => compare_ctor (Sexpr a)
      | Sattr a b => compare_ctor (Sattr a b)
      | Sasm a b c d e => compare_ctor (Sasm a b c d e)
      | Slabeled a b => compare_ctor (Slabeled a b)
      | Sgoto a => compare_ctor (Sgoto (lang:=lang) a)
      | Sunsupported a => compare_ctor (Sunsupported (lang:=lang) a)
      end.

  End compare_body.
End Stmt.


(* This is needed to speed up compilation on the guardedness check on the
   following [compare{N,T,E,VD,S}] functions. Without this, the termination
   checker *does succeed* but it takes ~800s.
 *)
#[local] Unset Guard Checking.

Section compare.
  Context {lang : lang.t}.
  #[local] Notation name := (name' lang).
  #[local] Notation type := (type' lang).
  #[local] Notation Expr := (Expr' lang).
  #[local] Notation VarDecl := (VarDecl' lang).
  #[local] Notation Stmt := (Stmt' lang).

  Fixpoint compareN (n : name) : name -> comparison :=
    name.compare_body compareN compareT compareE n

  with compareT (t : type) : type -> comparison :=
    type.compare_body compareN compareT compareE t

  with compareE (e : Expr) : Expr -> comparison :=
    Expr.compare_body compareN compareT compareE compareS e

  with compareVD (vd : VarDecl) : VarDecl -> comparison :=
    VarDecl.compare_body compareN compareT compareE compareVD vd

  with compareS (s : Stmt) : Stmt -> comparison :=
    Stmt.compare_body compareE compareVD compareS s
  .

End compare.

#[local] Set Guard Checking.

Section compare_instances.
  Context {lang : lang.t}.
  #[local] Notation name := (name' lang).
  #[local] Notation type := (type' lang).
  #[local] Notation Expr := (Expr' lang).
  #[local] Notation VarDecl := (VarDecl' lang).
  #[local] Notation Stmt := (Stmt' lang).

  #[global] Instance name_compare : Compare name := compareN.
  #[global] Instance type_compare : Compare type := compareT.
  #[global] Instance Expr_compare : Compare Expr := compareE.
  #[global] Instance VarDecl_compare : Compare VarDecl := compareVD.
  #[global] Instance Stmt_compare : Compare Stmt := compareS.

End compare_instances.

(** ** Name maps *)

#[global] Declare Instance name_comparison {lang} :
  Comparison (compareN (lang:=lang)).	(** TODO *)

Require Import Coq.Structures.OrderedTypeAlt.
Require Import Coq.FSets.FMapAVL.
Require Import bedrock.prelude.avl.

Module Type LANG.
  Parameter Inline lang : lang.t.
End LANG.

Module NameMap (Lang : LANG).
  Module Compare.
    Definition t : Type := name' Lang.lang.
    #[local] Definition compare : t -> t -> comparison := compareN.
    #[local] Infix "?=" := compare.
    #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
    Proof. exact: compare_antisym. Qed.
    #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
    Proof. exact: base.compare_trans. Qed.
  End Compare.
  Module Key := OrderedType_from_Alt Compare.
  Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
  Proof. Admitted.
  Include FMapAVL.Make Key.
  Include FMapExtra.MIXIN Key.
  Include FMapExtra.MIXIN_LEIBNIZ Key.
End NameMap.

Module NM.
  #[local] Definition lang := lang.cpp.
  Include NameMap.
End NM.

Module TM.
  #[local] Definition lang := lang.temp.
  Include NameMap.
End TM.

Definition table : Type := NM.t N.
Definition Dnum (n : name) (v : N) : table -> table :=
  <[ n := v ]>.
Definition test : table := Dnum (Nglobal $ Nid "cats") 3 ∅.
