(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Ltac2.Ltac2.
Require Export bluerock.prelude.base.	(* for, e.g., <<::>> *)
Require Import stdpp.sorting.
Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Require Import bluerock.prelude.parray.
Require Import bluerock.prelude.compare.
Require Import bluerock.prelude.uint63.
Require Export Stdlib.Strings.PrimString.
Require Import bluerock.prelude.avl.
Require Export bluerock.lang.cpp.syntax. (* NOTE: too much *)
Require bluerock.lang.cpp.semantics.sub_module.
Require Export bluerock.lang.cpp.parser.stmt.
Require Import bluerock.lang.cpp.parser.lang.
Require Import bluerock.lang.cpp.parser.type.
Require Import bluerock.lang.cpp.parser.name.
Require Import bluerock.lang.cpp.parser.expr.
Require Import bluerock.lang.cpp.parser.decl.
Require Import bluerock.lang.cpp.parser.notation.
Require Import bluerock.lang.cpp.parser.reduction.

Include ParserName.
Include ParserType.
Include ParserExpr.
Include ParserDecl.

Section unique_merge_sort.
  Context {A} (compare : A -> A -> comparison).
  (* Small variation on stdpp.sorting, TODO copyright. *)

  Fixpoint list_merge (l1 : list A) : list A → list A :=
    fix list_merge_aux l2 :=
    match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | x1 :: l1, x2 :: l2 =>
      match compare x1 x2 with
      | Lt => x1 :: list_merge l1 (x2 :: l2)
      | Eq => list_merge l1 (x2 :: l2)
      | Gt => x2 :: list_merge_aux l2
      end
    end.
  Global Arguments list_merge !_ !_ / : assert.

  Local Notation stack := (list (option (list A))).
  Fixpoint merge_list_to_stack (st : stack) (l : list A) : stack :=
    match st with
    | [] => [Some l]
    | None :: st => Some l :: st
    | Some l' :: st => None :: merge_list_to_stack st (list_merge l' l)
    end.
  Fixpoint merge_stack (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack st
    | Some l :: st => list_merge l (merge_stack st)
    end.
  Fixpoint merge_sort_aux (st : stack) (l : list A) : list A :=
    match l with
    | [] => merge_stack st
    | x :: l => merge_sort_aux (merge_list_to_stack st [x]) l
    end.
  Definition unique_merge_sort : list A → list A := merge_sort_aux [].

End unique_merge_sort.

Definition compare_rel {A} (compare : A -> A -> comparison) : relation A :=
  fun x1 x2 => compare x1 x2 = Lt.

Class SymmetricCompare {A : Type} (compare : Compare A) :=
  compare_symm :
    ∀ {x y : A}, compare x y = Lt <-> compare y x = Gt.

Section with_compare.
  Context {A} (compare : A -> A -> comparison).

  #[global] Instance compare_trichotomy
    `{!LeibnizComparison compare} `{!SymmetricCompare compare} :
    Trichotomy (compare_rel compare).
  Proof.
    move=> x y. case E: (compare x y); [auto..|].
    right; right. exact /compare_symm.
  Qed.

  (** ** Correctness of merge sort *)
  Section merge_sort_correct.

    Lemma list_merge_nil_l l2 : list_merge compare [] l2 = l2.
    Proof. by destruct l2. Qed.
    Lemma list_merge_nil_r l1 : list_merge compare l1 [] = l1.
    Proof. by destruct l1. Qed.
    Lemma list_merge_cons x1 x2 l1 l2 :
      list_merge compare (x1 :: l1) (x2 :: l2) =
        match compare x1 x2 with
        | Lt => x1 :: list_merge compare l1 (x2 :: l2)
        | Eq => list_merge compare l1 (x2 :: l2)
        | Gt => x2 :: list_merge compare (x1 :: l1) l2
        end.
    Proof. done. Qed.

    Notation R := (compare_rel compare).

  (* Lemma compare_symm (x y : A) `{!SymmetricCompare compare} :
    compare x y = Lt <-> compare y x = Gt.
  Proof.
    split; first exact: compare_symm_lt.
    destruct (compare x y). *)

    Context `{!LeibnizComparison compare} `{!SymmetricCompare compare}.

    (*
    Instance: Trichotomy R := compare_trichotomy.
    Proof.
      move=> x y. rewrite /R.
      destruct (compare x y) eqn:?; info_auto.
      right; right; exact /compare_symm.
    Qed.
    apply (LeibnizComparison.cmp_eq compare _ _ Heqc).
    *)

(* From stdpp Require Import options. *)
  (* Let R : relation A := fun x1 x2 => compare x1 x2 = Lt \/ compare x1 x2 = Eq. *)
  (*
  Lemma HdRel_list_merge x l1 l2 :
    HdRel R x l1 → HdRel R x l2 → HdRel R x (list_merge compare l1 l2).
  Proof.
    destruct 1 as [|x1 l1 IH1], 1 as [|x2 l2 IH2];
      rewrite ?list_merge_cons; simpl; repeat case_match; auto.
      Print HdRel.
      econstructor.
  Qed. *)
  (*
  Lemma Sorted_list_merge `{!Trichotomy R} l1 l2 :
    Sorted R l1 → Sorted R l2 → Sorted R (list_merge compare l1 l2).
  Proof.
    intros Hl1. revert l2. induction Hl1 as [|x1 l1 IH1];
      induction 1 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_match;
      (* repeat case_decide;
      repeat match goal with H : ¬R _ _ |- _ => apply total_not in H end; *)
      try constructor; eauto using HdRel_cons.
  Lemma HdRel_list_merge x l1 l2 :
  Sorted R l2 ->
    HdRel R x l1 → HdRel R x l2 → HdRel R x (list_merge compare l1 l2).
  Proof.
    revert l1; induction l2 as [|x2 l2 IHl2] => l1.
    destruct 2 as [|x1 l1 IH1];
    inversion_clear 1;
      rewrite ?list_merge_cons /=; repeat case_match; auto.
    inversion 1 as [|x2 l2 IH2].
      rewrite ?list_merge_cons; simpl; repeat case_match; auto.
      econstructor.
  Qed.

      Print HdRel.
      rewrite list_merge_cons.
      (* all: eauto using HdRel_list_merge, HdRel_cons. *)
  Qed.
  Lemma merge_Permutation l1 l2 : list_merge R l1 l2 ≡ₚ l1 ++ l2.
  Proof.
    revert l2. induction l1 as [|x1 l1 IH1]; intros l2;
      induction l2 as [|x2 l2 IH2]; rewrite ?list_merge_cons; simpl;
      repeat case_decide; auto.
    - by rewrite (right_id_L [] (++)).
    - by rewrite IH2 Permutation_middle.
  Qed.

  Local Notation stack := (list (option (list A))).
  Inductive merge_stack_Sorted : stack → Prop :=
    | merge_stack_Sorted_nil : merge_stack_Sorted []
    | merge_stack_Sorted_cons_None st :
       merge_stack_Sorted st → merge_stack_Sorted (None :: st)
    | merge_stack_Sorted_cons_Some l st :
       Sorted R l → merge_stack_Sorted st → merge_stack_Sorted (Some l :: st).
  Fixpoint merge_stack_flatten (st : stack) : list A :=
    match st with
    | [] => []
    | None :: st => merge_stack_flatten st
    | Some l :: st => l ++ merge_stack_flatten st
    end.

  Lemma Sorted_merge_list_to_stack `{!Total R} st l :
    merge_stack_Sorted st → Sorted R l →
    merge_stack_Sorted (merge_list_to_stack R st l).
  Proof.
    intros Hst. revert l.
    induction Hst; repeat constructor; naive_solver auto using Sorted_list_merge.
  Qed.
  Lemma merge_list_to_stack_Permutation st l :
    merge_stack_flatten (merge_list_to_stack R st l) ≡ₚ
      l ++ merge_stack_flatten st.
  Proof.
    revert l. induction st as [|[l'|] st IH]; intros l; simpl; auto.
    by rewrite IH, merge_Permutation, (assoc_L _), (comm (++) l).
  Qed.
  Lemma Sorted_merge_stack `{!Total R} st :
    merge_stack_Sorted st → Sorted R (merge_stack R st).
  Proof. induction 1; simpl; auto using Sorted_list_merge. Qed.
  Lemma merge_stack_Permutation st : merge_stack R st ≡ₚ merge_stack_flatten st.
  Proof.
    induction st as [|[] ? IH]; intros; simpl; auto.
    by rewrite merge_Permutation, IH.
  Qed.
  Lemma Sorted_merge_sort_aux `{!Total R} st l :
    merge_stack_Sorted st → Sorted R (merge_sort_aux R st l).
  Proof.
    revert st. induction l; simpl;
      auto using Sorted_merge_stack, Sorted_merge_list_to_stack.
  Qed.
  Lemma merge_sort_aux_Permutation st l :
    merge_sort_aux R st l ≡ₚ merge_stack_flatten st ++ l.
  Proof.
    revert st. induction l as [|?? IH]; simpl; intros.
    - by rewrite (right_id_L [] (++)), merge_stack_Permutation.
    - rewrite IH, merge_list_to_stack_Permutation; simpl.
      by rewrite Permutation_middle.
  Qed.
  Lemma Sorted_merge_sort `{!Total R} l : Sorted R (merge_sort R l).
  Proof. apply Sorted_merge_sort_aux. by constructor. Qed.
  Lemma merge_sort_Permutation l : merge_sort R l ≡ₚ l.
  Proof. unfold merge_sort. by rewrite merge_sort_aux_Permutation. Qed.
  Lemma StronglySorted_merge_sort `{!Transitive R, !Total R} l :
    StronglySorted R (merge_sort R l).
  Proof. auto using Sorted_StronglySorted, Sorted_merge_sort. Qed.
  *)
  End merge_sort_correct.
End with_compare.

Module Import translation_unit.

  (**
  We work with an exploded [translation_unit] and raw trees for
  efficiency.
  *)

  Definition raw_symbol_table : Type := NM.Raw.t ObjValue.
  Definition raw_type_table : Type := NM.Raw.t GlobDecl.

  #[global] Instance raw_structured_insert : forall {T}, Insert globname T (NM.Raw.t T) := _.

  Definition dup_info := list (name * (GlobDecl + ObjValue)).
  (** This representation is isomorphic to [translation_unit * list name] as shown by [decls]. *)
  Definition t : Type :=
    raw_symbol_table -> raw_type_table -> dup_info ->
    (raw_symbol_table -> raw_type_table -> dup_info -> translation_unit * dup_info) ->
    translation_unit * dup_info.

  Definition merge_obj_value (a b : ObjValue) : option ObjValue :=
    if sub_module.ObjValue_le a b then
      Some b
    else if sub_module.ObjValue_le b a then Some a
         else None.

  (** Constructs a [translation_unit.t] with _one_ symbol, mapping [n] to [v]. *)
  Definition _symbols (n : name) (v : ObjValue) : t :=
    fun s t dups k =>
      match s !! n with
      | None => k (<[n := v]> s) t dups
      | Some v' => match merge_obj_value v v' with
                  | Some v => k (<[n:=v]> s) t dups
                  | None => k s t ((n, inr v) :: (n, inr v') :: dups)
                  end
      end.
  Definition merge_glob_decl (a b : GlobDecl) : option GlobDecl :=
    if sub_module.GlobDecl_le a b then
      Some b
    else if sub_module.GlobDecl_le b a then Some a
         else None.

  (** Constructs a [translation_unit.t] with _one_ type, mapping [n] to [v]. *)
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
                    | None => k s t ((n, inl v) :: (n, inl v') :: dups)
                    end
        end.

  Definition _aliases (n : name) (ty : type) : t :=
    _types n (Gtypedef ty).

  (** Constructs an empty [translation_unit.t]. *)
  Definition _skip : t :=
    fun s t dups k => k s t dups.

  Fixpoint array_fold {A B}
    (f : A -> B -> B) (ar : PArray.array A) (fuel : nat) (i : PrimInt63.int) (acc : B) : B :=
    match fuel with
    | 0 => acc
    | S fuel =>
        array_fold f ar fuel (PrimInt63.add i 1) (f (PArray.get ar i) acc)
    end.

  Definition abi_type := endian.

  Definition decls' (ds : PArray.array t) : t :=
    array_fold (fun (X Y : t) s t dups K => X s t dups (fun s t dups => Y s t dups K))
      ds
      (Z.to_nat (Uint63.to_Z (PArray.length ds))) 0%uint63
      (fun s t dups k => k s t dups).

  Definition decls (ds : PArray.array t) (e : abi_type) : translation_unit * dup_info :=
    decls' ds ∅ ∅ [] $ fun s t => pair {|
      symbols := NM.from_raw s;
      types := NM.from_raw t;
      initializer := nil;	(** TODO *)
      byte_order := e;
    |}.

  Definition list_decls (ls : list translation_unit.t) :=
    decls $ PArray.of_list _skip ls.

  Module make.
    Import Ltac2.Ltac2.

    Ltac2 Type exn ::= [DuplicateSymbols (constr)].

    (* [check_translation_unit tu]
     *)
    Ltac2 check_translation_unit (tu : preterm) (en : preterm) :=
      let endian := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype '(endian)) en in
      let tu := Constr.Pretype.pretype Constr.Pretype.Flags.constr_flags (Constr.Pretype.expected_oftype '(PArray.array t)) tu in
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

Definition Dvariable (n : obj_name) (t : type) (init : global_init.t) : K :=
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
