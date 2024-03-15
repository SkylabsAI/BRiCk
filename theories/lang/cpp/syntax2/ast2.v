(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.cpp.syntax2.prelude.
Require Import bedrock.prelude.avl.
Require Import bedrock.lang.cpp.syntax2.syntax1.
Require Import bedrock.lang.cpp.syntax2.overloadable.

#[local] Set Primitive Projections.

(** ** Function types *)
(**
TODO: Prefer [function_type] over [functype]. This is complicated by
the several function-like things in the language, with quirky rules
(e.g., member functions may be adorned with qualifiers governing how
<<this>> works and constructors/destructors aren't member functions).
*)
Record function_type' {decltype : Set} : Set := FunctionType {
  ft_cc : calling_conv;
  ft_arity : function_arity;
  ft_return : decltype;
  ft_params : list decltype;
}.
Add Printing Constructor function_type'.
#[global] Arguments function_type' : clear implicits.
#[global] Arguments FunctionType {_ _ _} _ _ : assert.
#[global] Instance function_type'_inhabited {A : Set} {_ : Inhabited A} : Inhabited (function_type' A).
Proof. solve_inhabited. Qed.
#[global] Instance function_type'_eq_dec {A : Set} {_ : EqDecision A} : EqDecision (function_type' A).
Proof. solve_decision. Defined.

Module function_type.
  Definition existsb {decltype : Set} (f : decltype -> bool)
      (ft : function_type' decltype) : bool :=
    f ft.(ft_return) || existsb f ft.(ft_params).
End function_type.

(** ** Templates *)

Variant temp_param' {type : Set} : Set :=
| Ptype (_ : ident)
| Pvalue (_ : ident) (_ : type)
| Punsupported (_ : bs).
#[global] Arguments temp_param' : clear implicits.
#[global] Instance temp_param_inhabited {A} : Inhabited (temp_param' A).
Proof. solve_inhabited. Qed.
#[global] Instance temp_param_eq_dec {A : Set} `{!EqDecision A} : EqDecision (temp_param' A).
Proof. solve_decision. Defined.

Module temp_param.
  Definition existsb {type : Set} (f : type -> bool) (p : temp_param' type) : bool :=
    if p is Pvalue _ t then f t else false.
End temp_param.

Variant temp_arg' {decltype Expr : Set} : Set :=
| Atype (_ : decltype)
| Avalue (_ : Expr)
| Aunsupported (_ : bs).
Arguments temp_arg' : clear implicits.
#[global] Instance temp_arg'_inhabited {A B : Set} {_ : Inhabited A} : Inhabited (temp_arg' A B).
Proof. solve_inhabited. Qed.
#[global] Instance temp_arg'_eq_dec {A B : Set} {_ : EqDecision A} {_ : EqDecision B} : EqDecision (temp_arg' A B).
Proof. solve_decision. Defined.

Module temp_arg.
  Definition existsb {type Expr : Set} (f : type -> bool) (g : Expr -> bool)
      (a : temp_arg' type Expr) : bool :=
    match a with
    | Atype t => f t
    | Avalue e => g e
    | Aunsupported _ => false
    end.
End temp_arg.

(** ** Function names and qualifiers *)
Variant function_name' {type : Set} : Set :=
| Nf (_ : ident)
| Nctor
| Ndtor
| Nop (_ : OverloadableOperator)
| Nop_conv (_ : type)
| Nop_lit (_ : ident)
| Nunsupported_function (_ : bs).
#[global] Arguments function_name' : clear implicits.
#[global] Instance function_name_inhabited {A} : Inhabited (function_name' A).
Proof. solve_inhabited. Qed.
#[global] Instance function_name_eq_dec {A : Set} `{!EqDecision A} : EqDecision (function_name' A).
Proof. solve_decision. Defined.

Module function_name.
  Definition existsb {type : Set} (f : type -> bool) (n : function_name' type) : bool :=
    if n is Nop_conv t then f t else false.
End function_name.

Variant function_qualifier : Set :=
| Nconst	(** <<const>> *)
| Nvolatile	(** <<volatile>> *)
| Nnoexcept	(** <<noexcept>> *)
| Nlvalue	(** <<&>> *)
| Nrvalue	(** <<&&>> *)
.
#[global] Instance function_qualifier_inhabited : Inhabited function_qualifier.
Proof. solve_inhabited. Qed.
#[global] Instance function_qualifier_eq_dec : EqDecision function_qualifier.
Proof. solve_decision. Defined.

(** ** Atomic names *)
(**
Atomic names are effectively path components.
*)
Variant atomic_name' {type Expr : Set} : Set :=
(** Named things *)
| Nid (_ : ident)	(** namespace, struct, union, typedef, variable, member, ... *)
(**
NOTE: [Nfunction] should take a set of qualifiers but [gset] has an
opaque empty instance (interfering with reduction) and [listset] lacks
an [EqDecision] instance. Cpp2v emits qualifiers in a specific order
to enable pattern to use Leibniz equality.

TODO: Add a varargs bit (perhaps to <<function_qualifier>>) for
trailing <<...>>> in argument types.

TODO (Discuss): Do we need to distinguish templated functions by their
return types?
*)
| Nfunction (_ : list function_qualifier) (_ : function_name' type) (_ : list type)
(** Unnamed things *)
(**
TODO: We should generalize <<Ndecltype>> to <<Ndependent (_ : type)>>
to enable (say) <<Tparam>> in a declaration's context. This may also
let us replace some uses of <<classname>> in declarations with
<<name>>.
*)
| Ndecltype (id : bool) (_ : Expr)
| Nclosure (_ : list type)
| Nanon (_ : N)
(** Errors *)
| Nunsupported_atomic (_ : bs).
#[global] Arguments atomic_name' : clear implicits.
#[global] Instance atomic_name_inhabited {A B} : Inhabited (atomic_name' A B).
Proof. solve_inhabited. Qed.
#[global] Instance atomic_name_eq_dec {A B : Set} `{!EqDecision A, !EqDecision B} : EqDecision (atomic_name' A B).
Proof. solve_decision. Defined.

Module atomic_name.
  Definition existsb {type Expr : Set} (f : type -> bool) (g : Expr -> bool)
      (c : atomic_name' type Expr) : bool :=
    match c with
    | Nid _ => false
    | Nfunction _ n ts => function_name.existsb f n || List.existsb f ts
    | Ndecltype _ e => g e
    | Nclosure ts => List.existsb f ts
    | Nanon _
    | Nunsupported_atomic _ => false
    end.
End atomic_name.

(** ** Structured names *)
Inductive name {lang : Set} : Set :=
| Ninst (c : name) (_ : list (temp_arg' type Expr))
| Nglobal (c : atomic_name' type Expr)	(* <<::c>> *)
| Nscoped (n : name) (c : atomic_name' type Expr)	(* <<n::c>> *)
| Nunsupported (_ : bs)

(** ** Types *)
(**
NOTE: We could eliminate [Tresult_unop], [Tresult_binop] using
[Tresult_call] because the evaluation order distinction between
operators and operator calls does not matter for typing purposes. We
do things this way for consistency, and to keep the components of
substitutions small.
*)

with type {lang : Set} : Set :=
| Tparam (_ : ident)
| Tresult_param (_ : ident)
| Tresult_global (on : name)
| Tresult_unop (_ : RUnOp) (_ : type)
| Tresult_binop (_ : RBinOp) (_ _ : type)
| Tresult_call (on : name) (_ : list type)
| Tresult_member_call (on : name) (_ : type) (_ : list type)
| Tresult_parenlist (_ :type) (_ : list type)
| Tresult_member (_ : type) (_ : ident)

| Tptr (t : type)
| Tref (t : type)
| Trv_ref (t : type)
| Tnum (sz : bitsize) (sgn : signed)
| Tchar_ (_ : char_type.t)
| Tvoid
| Tarray (t : type) (n : N)
| Tincomplete_array (t : type)
| Tvariable_array (t : type) (e : Expr)
| Tnamed (gn : name)
| Tenum (gn : name)
| Tfunction (t : function_type' type)
| Tbool
(**
TODO: The class should be a full [type] to permit (say) [Tparam].
*)
| Tmember_pointer (gn : name) (t : type)
| Tfloat_ (_ : float_type.t)
| Tqualified (q : type_qualifiers) (t : type)
| Tnullptr
| Tarch (osz : option bitsize) (name : bs)
| Tdecltype (_ : Expr)
| Tunsupported (_ : bs)

(** ** Expressions *)
(**
NOTE: We need both unresolved operators and unresolved calls because
operators like <<a = b>> use a different evaluation order than calls
like <<operator=(a, b)>>.
*)
with Expr {lang : Set} : Set :=
| Eparam (_ : ident)
| Eunresolved_global (_ : name)
| Eunresolved_unop (_ : RUnOp) (e : Expr)
| Eunresolved_binop (_ : RBinOp) (l r : Expr)
| Eunresolved_call (on : name) (_ : list Expr)
| Eunresolved_member_call (on : name) (_ : Expr) (_ : list Expr)
(**
<<Eunresolved_parenlist (Some T) [arg1;…;argN]>> is the initializer
for an uninstantiated direct initializer list declaration <<T
var(arg1,…,argN)>> with dependent type <<T>>. Making the type optional
simplifies cpp2v---we set it from context in ../mparser2.v.
*)
| Eunresolved_parenlist (_ : option type) (_ : list Expr)
| Eunresolved_member (_ : Expr) (_ : ident)

(**
NOTE: We might need to support template parameters as object names in
a few constructors (by carrying <<Expr ≈ Eparam + Eglobal>> instead of
<<name>>).
*)

| Evar (_ : localname) (_ : type)
| Eenum_const (gn : name) (_ : ident)
| Eglobal (on : name) (_ : type)

| Echar (c : N) (t : type)
| Estring (s : list N) (t : type)
| Eint (n : Z) (t : type)
| Ebool (b : bool)
| Eunop (op : UnOp) (e : Expr) (t : type)
| Ebinop (op : BinOp) (e1 e2 : Expr) (t : type)
| Ederef (e : Expr) (t : type)
| Eaddrof (e : Expr)
| Eassign (e1 e2 : Expr) (t : type)
| Eassign_op (op : BinOp) (e1 e2 : Expr) (t : type)
| Epreinc (e : Expr) (t : type)
| Epostinc (e : Expr) (t : type)
| Epredec (e : Expr) (t : type)
| Epostdec (e : Expr) (t : type)
| Eseqand (e1 e2 : Expr)
| Eseqor (e1 e2 : Expr)
| Ecomma (e1 e2 : Expr)
| Ecall (f : Expr) (es : list Expr)
(**
TODO (FM-4320): <<Cdependent>> may require care
*)
| Ecast (c : Cast' type name type) (e : Expr) (vc : ValCat) (t : type)
| Emember (obj : Expr) (f : ident) (mut : bool) (t : type)
| Emember_call (method : MethodRef' name type Expr) (obj : Expr) (args : list Expr)
| Eoperator_call (_ : OverloadableOperator) (_ : operator_impl.t name type) (_ : list Expr)
| Esubscript (e1 : Expr) (e2 : Expr) (t : type)
| Esizeof (_ : type + Expr) (t : type)
| Ealignof (_ : type + Expr) (t : type)
(**
NOTE: [Eoffsetof] carries a type instead of a name to support
dependent types.
*)
| Eoffsetof (gn : type) (_ : ident) (t : type)
| Econstructor (on : name) (args : list Expr) (t : type)
| Eimplicit (e : Expr)
| Eimplicit_init (t : type)
| Eif (e1 e2 e3 : Expr) (vc : ValCat) (t : type)
| Eif2  (n : N) (common cond thn els : Expr) (_ : ValCat) (_ : type)
| Ethis (t : type)
| Enull
| Einitlist (args : list Expr) (default : option Expr) (t : type)
| Enew (new_fn : name * type) (new_args : list Expr) (pass_align : new_form)
  (alloc_ty : type) (array_size : option Expr) (init : option Expr)
| Edelete (is_array : bool) (del_fn : name * type)
  (arg : Expr) (deleted_type : type)
| Eandclean (e : Expr)
| Ematerialize_temp (e : Expr) (vc : ValCat)
| Eatomic (op : AtomicOp) (args : list Expr) (t : type)
| Eva_arg (e : Expr) (t : type)
  (**
  TODO: We may have to adjust cpp2v: Either [Eva_arg] should carry a
  decltype, or [valcat_of] in cpp2v-core and [decltype.of_expr] here
  are unnecessarily complicated.

  See [valcat_of] in cpp2v-core.

  TODO: [Eva_arg _ Tdependent]

  Docs for <<__builtin_va_arg>>.
  https://clang.llvm.org/docs/LanguageExtensions.html#builtin-functions
  *)
| Epseudo_destructor (is_arrow : bool) (t : type) (e : Expr)
| Earrayloop_init (oname : N) (src : Expr) (level : N) (length : N) (init : Expr) (t : type)
| Earrayloop_index (level : N) (t : type)
| Eopaque_ref (name : N) (vc : ValCat) (t : type)
| Eunsupported (s : bs) (vc : ValCat) (t : type).

#[global] Arguments name : clear implicits.
#[global] Arguments type : clear implicits.
#[global] Arguments Expr : clear implicits.

#[global] Instance type_inhabited {lang} : Inhabited (type lang).
Proof. solve_inhabited. Qed.
#[global] Instance Expr_inhabited {lang} : Inhabited (Expr lang).
Proof. solve_inhabited. Qed.
#[global] Instance name_inhabited {lang} : Inhabited (name lang).
Proof. apply populate, Nglobal, inhabitant. Qed.

Section eq_dec.
  Context {lang : Set}.
  #[local] Notation EQ_DEC T := (∀ x y : T, Decision (x = y)) (only parsing).

  Lemma name_eq_dec' : EQ_DEC (name lang)
  with type_eq_dec' : EQ_DEC (type lang)
  with Expr_eq_dec' : EQ_DEC (Expr lang).
  Proof.
    all: intros x y.
    all: pose (name_eq_dec' : EqDecision _).
    all: pose (type_eq_dec' : EqDecision _).
    all: pose (Expr_eq_dec' : EqDecision _).
    all:unfold Decision; decide equality; solve_decision.
  Defined.

  #[global] Instance name_eq_dec : EqDecision _ := name_eq_dec'.
  #[global] Instance type_eq_dec : EqDecision _ := type_eq_dec'.
  #[global] Instance Expr_eq_dec : EqDecision _ := Expr_eq_dec'.
End eq_dec.

Variant cpp : Set :=.	(* phantom type *)
Variant temp : Set :=.	(* phantom type *)

Definition is_implicit {lang} (e : Expr lang) : bool :=
  if e is Eimplicit _ then true else false.

Definition globname := name.	(** Type names *)
Definition obj_name := name.	(** Function, data names *)

Definition exprtype := type.	(** An expression's non-reference type *)
Definition decltype := type.	(** Types as used in declarations (≈ ValCat × exprtype) *)
Definition functype := type.	(** Must be [Tfunction] *)

(**
NOTE: For the moment, we use <<classname>> rather than <<name>> in a
few declarations to account for possibly dependent names.

- For core C++, we pick <<classname := Sname>>.

- For templates, we pick <<classname := Mtype>> permitting
non-dependent names via <<Tnamed>> and dependent names via <<Tparam>>.
(Substitution resolves <<Mclassname>> to <<Sname>>.)

We are likely to add <<Ndependent (_ : type) : atomic_name>> to
account for dependent scopes. That addition would likely permit us to
collapse the <<classname>> vs <<name>> distinction.

TODO: We might need to similarly replace a few uses of <<name>> by
<<Expr>> in our syntax to support dependent function and variable
names.
*)

(** ** Template pre-instances *)
(**
A template file maps the symbol or type name of a template
instantiation (bound in a translation unit) to a _template
pre-instance_ comprising the instance's template name (bound in a
template file) and arguments.
*)
Definition temp_name : Set := bs.
Bind Scope bs_scope with temp_name.
Section tpreinst.
  Context {decltype Expr : Set}.

  Record tpreinst' : Set := TPreInst {
    tpreinst_name : temp_name;
    tpreinst_args : list (temp_arg' decltype Expr);
  }.

  #[global] Instance tpreinst'_inhabited : Inhabited tpreinst'.
  Proof. solve_inhabited. Qed.

  #[global] Instance tpreinst'_eq_dec `{!EqDecision decltype, !EqDecision Expr} :
    EqDecision tpreinst'.
  Proof. solve_decision. Defined.
End tpreinst.
Add Printing Constructor tpreinst'.
#[global] Arguments tpreinst' : clear implicits.
#[global] Arguments TPreInst {_ _} _ & _ : assert.

(** ** Template instances *)
Section tinst.
  #[local] Set Universe Polymorphism.
  #[local] Set Polymorphic Inductive Cumulativity.
  #[local] Unset Auto Template Polymorphism.
  Universe uV.
  Context {decltype Expr : Set} {V : Type@{uV}}.

  Record tinst' : Type@{uV} := TInst {
    tinst_params : list (temp_param' (type temp));
    tinst_args : list (temp_arg' decltype Expr);
    tinst_value : V;
  }.

  #[global] Instance tinst'_inhabited `{!Inhabited V} : Inhabited tinst'.
  Proof. solve_inhabited. Qed.

  #[global] Instance tinst'_eq_dec
      `{!EqDecision decltype, !EqDecision Expr, !EqDecision V} :
    EqDecision tinst'.
  Proof. solve_decision. Defined.
End tinst.
Add Printing Constructor tinst'.
#[global] Arguments tinst' : clear implicits.
#[global] Arguments TInst {_ _ _} _ _ & _ : assert.

(**
TODO: Some of these are not parametric in <<lang>> because
<<Mclassname := Mtype>>, <<Sclassname := Sname>>.
*)
Module Import LangNotations.

  (**
  We cannot use these definitions in our notations _and_ preserve
  those notations after hitting terms with, e.g., <<eval compute>>.
  *)
  #[local] Notation decltype := type (only parsing).
  #[local] Notation exprtype := type (only parsing).
  #[local] Notation obj_name := name (only parsing).
  #[local] Notation globname := name (only parsing).

  Notation Cast lang := (Cast' (type lang) (name lang) (type lang)).
  Notation operator_impl lang := (operator_impl.t (name lang) (type lang)).
  Notation MethodRef lang := (MethodRef' (name lang) (type lang) (Expr lang)).

  Notation function_type lang := (function_type' (type lang)).
  Notation temp_param lang := (temp_param' (type lang)).
  Notation temp_arg lang := (temp_arg' (type lang) (Expr lang)).
  Notation function_name lang := (function_name' (type lang)).
  Notation atomic_name lang := (atomic_name' (type lang) (Expr lang)).
  Notation tpreinst lang := (tpreinst' (decltype lang) (Expr lang)).
  Notation tinst lang := (tinst' (decltype lang) (Expr lang)).

  Notation VarDecl lang := (VarDecl' (obj_name lang) (decltype lang) (Expr lang)).
  Notation Stmt lang := (Stmt' (obj_name lang) (decltype lang) (Expr lang)).

  Notation FunctionBody lang := (FunctionBody' (obj_name lang) (decltype lang) (Expr lang)).
  Notation Func lang := (Func' (obj_name lang) (decltype lang) (Expr lang)).
  Notation GlobalInit lang := (GlobalInit' (Expr lang)).
  Notation GlobalInitializer lang := (GlobalInitializer' (obj_name lang) (decltype lang) (Expr lang)).
  Notation InitializerBlock lang := (InitializerBlock' (obj_name lang) (decltype lang) (Expr lang)).
End LangNotations.

(** ** C++ with structured names *)
Notation Sname := (name cpp).
Notation Sglobname := (globname cpp).
Notation Sobj_name := (obj_name cpp).
Notation Stype := (type cpp).
Notation Sexprtype := (exprtype cpp).
Notation Sdecltype := (decltype cpp).
Notation SCast := (Cast cpp).
Notation Soperator_impl := (operator_impl cpp).
Notation SMethodRef := (MethodRef cpp).
Notation SExpr := (Expr cpp).
Notation Sfunction_type := (function_type cpp).
Notation Stemp_param := (temp_param cpp).
Notation Stemp_arg := (temp_arg cpp).
Notation Sfunction_name := (function_name cpp).
Notation Satomic_name := (atomic_name cpp).
Notation SVarDecl := (VarDecl cpp).
Notation SStmt := (Stmt cpp).
Notation SMember := (Member' Sname Stype SExpr).
Notation SUnion := (Union' Sname Sname Stype SExpr).
Notation SStruct := (Struct' Sname Sname Stype SExpr).
Notation SFunctionBody := (FunctionBody cpp).
Notation SFunc := (Func cpp).
Notation SMethod := (Method' Sname Sname Stype SExpr).
Notation Sfield_name := (field_name.t Sname).
Notation SInitPath := (InitPath' Sname).
Notation SInitializer := (Initializer' Sname Stype SExpr).
Notation SCtor := (Ctor' Sname Sname Stype SExpr).
Notation SDtor := (Dtor' Sname Sname Stype SExpr).
Notation SObjValue := (ObjValue' Sname Sname Stype SExpr).
Notation SGlobDecl := (GlobDecl' Sname Sname Stype SExpr).
Notation SGlobalInit := (GlobalInit cpp).
Notation SGlobalInitializer := (GlobalInitializer cpp).
Notation SInitializerBlock := (InitializerBlock cpp).
Notation Stpreinst := (tpreinst cpp).
Notation Stinst := (tinst cpp).

(** ** Translation units *)
(**
A [translation_unit] value represents all the statically known
information about a C++ translation unit, that is, a source file.

TOOD: add support for symbols with _internal_ linkage.

TODO: does linking induce a (non-commutative) monoid on object files?
Is then a translation unit a "singleton" value in this monoid?
*)

Definition symbol_table : Type := IM.t SObjValue.
Definition type_table : Type := IM.t SGlobDecl.
Definition alias_table : Type := IM.t Stype.
Record translation_unit : Type := {
  symbols : symbol_table;
  types : type_table;
  aliases : alias_table;	(* we eschew <<Gtypedef>> for now *)
  initializer : SInitializerBlock;
  byte_order  : endian;
}.

(** ** Derived forms *)
Definition Qconst_volatile {lang} : type lang -> type lang :=
  Tqualified QCV.
Definition Qconst {lang} : type lang -> type lang :=
  Tqualified QC.
Definition Qmut_volatile {lang} : type lang -> type lang :=
  Tqualified QV.
Definition Qmut {lang} : type lang -> type lang :=
  Tqualified QM.

Notation Tchar := (Tchar_ char_type.Cchar).
Notation Twchar := (Tchar_ char_type.Cwchar).
Notation Tchar8 := (Tchar_ char_type.C8).
Notation Tchar16 := (Tchar_ char_type.C16).
Notation Tchar32 := (Tchar_ char_type.C32).

Notation Ti8 := (Tnum W8 Signed).
Notation Tu8 := (Tnum W8 Unsigned).
Notation Ti16 := (Tnum W16 Signed).
Notation Tu16 := (Tnum W16 Unsigned).
Notation Ti32 := (Tnum W32 Signed).
Notation Tu32 := (Tnum W32 Unsigned).
Notation Ti64 := (Tnum W64 Signed).
Notation Tu64 := (Tnum W64 Unsigned).
Notation Ti128 := (Tnum W128 Signed).
Notation Tu128 := (Tnum W128 Unsigned).

Notation Tschar := (Tnum int_type.Ichar Signed) (only parsing).
Notation Tuchar := (Tnum int_type.Ichar Unsigned) (only parsing).

Notation Tushort := (Tnum int_type.Ishort Unsigned) (only parsing).
Notation Tshort := (Tnum int_type.Ishort Signed) (only parsing).

Notation Tint := (Tnum int_type.Iint Signed) (only parsing).
Notation Tuint := (Tnum int_type.Iint Unsigned) (only parsing).

Notation Tulong := (Tnum int_type.Ilong Unsigned) (only parsing).
Notation Tlong := (Tnum int_type.Ilong Signed) (only parsing).

Notation Tulonglong := (Tnum int_type.Ilonglong Unsigned) (only parsing).
Notation Tlonglong := (Tnum int_type.Ilonglong Signed) (only parsing).

(** ** Qualifier normalization *)
(**
[decompose_type t] strips any top-level qualifiers from [t] and
returns them, paired with the rest of the type.

The underlying functions [qual_norm] and [qual_norm'] are similar
(see, e.g., [qual_norm_decompose_type]).
*)

Section qual_norm.
  Context {lang : Set} {A : Type}.
  Variable f : type_qualifiers -> type lang -> A.

  Fixpoint qual_norm' (q : type_qualifiers) (t : type lang) : A :=
    match t with
    | Tqualified q' t => qual_norm' (merge_tq q q') t
    | _ => f q t
    end.
  #[global] Hint Opaque qual_norm' : typeclass_instances.

  Definition qual_norm : type lang -> A :=
    qual_norm' QM.
  #[global] Hint Opaque qual_norm : typeclass_instances.
End qual_norm.

Definition decompose_type {lang} : type lang -> type_qualifiers * type lang :=
  qual_norm (fun q t => (q, t)).
#[global] Hint Opaque decompose_type : typeclass_instances.
#[global] Arguments decompose_type _ !_ / : simpl nomatch, assert.

(**
[take_qualifiers], [drop_qualifiers] return and remove leading
qualifiers.
*)
Definition take_qualifiers {lang} : type lang -> type_qualifiers :=
  qual_norm (fun cv _ => cv).

Fixpoint drop_qualifiers {lang} (t : type lang) : type lang :=
  match t with
  | Tqualified _ t => drop_qualifiers t
  | _ => t
  end.

(**
[drop_reference] removes any leading reference types.
*)
Fixpoint drop_reference {lang} (t : type lang) : exprtype lang :=
  match drop_qualifiers t with
  | Tref u | Trv_ref u => drop_reference u
  | _ => t	(* We do not normalize qualifiers here to promote sharing *)
  end.

(** ** Smart constructors *)

(**
Qualify a type, merging nested qualifiers, suppressing [QM]
qualifiers, and (https://www.eel.is/c++draft/dcl.ref#1) discarding any
cv-qualifiers on reference types.
*)
Definition tqualified' {lang} (q : type_qualifiers) (t : type lang) : type lang :=
  match t with
  | Tref _ | Trv_ref _ => t
  | _ => match q with QM => t | _ => Tqualified q t end
  end.
#[global] Hint Opaque tqualified' : typeclass_instances.
#[global] Arguments tqualified' _ _ !_ / : simpl nomatch, assert.

Definition tqualified {lang} : type_qualifiers -> type lang -> type lang :=
  qual_norm' tqualified'.
#[global] Hint Opaque tqualified : typeclass_instances.
#[global] Arguments tqualified _ _ !_ / : simpl nomatch, assert.

(**
[tref], [trv_ref] implement reference collapsing.

Background:
https://en.cppreference.com/w/cpp/language/reference#Reference_collapsing
https://www.eel.is/c++draft/dcl.ref#6
https://www.eel.is/c++draft/dcl.ref#5
*)
Definition tref {lang} := fix tref (acc : type_qualifiers) (t : type lang) : type lang :=
  match t with
  | Tref t | Trv_ref t => tref QM t
  | Tqualified q t => tref (merge_tq acc q) t
  | _ => Tref (tqualified acc t)
  end.
#[global] Hint Opaque tref : typeclass_instances.
#[global] Arguments tref _ _ !_ / : simpl nomatch, assert.

Definition trv_ref {lang} := fix trv_ref (acc : type_qualifiers) (t : type lang) : type lang :=
  match t with
  | Tref t => tref QM t
  | Trv_ref t => trv_ref QM t
  | Tqualified q t => trv_ref (merge_tq acc q) t
  | _ => Trv_ref (tqualified acc t)
  end.
#[global] Hint Opaque trv_ref : typeclass_instances.
#[global] Arguments trv_ref _ _ !_ / : simpl nomatch, assert.

(** ** Dependent names, types, and terms *)

Fixpoint is_dependentN {lang} (n : name lang) : bool :=
  match n with
  | Ninst n xs => is_dependentN n || existsb (temp_arg.existsb is_dependentT is_dependentE) xs
  | Nglobal c => atomic_name.existsb is_dependentT is_dependentE c
  | Nscoped n c => is_dependentN n || atomic_name.existsb is_dependentT is_dependentE c
  | Nunsupported _ => false
  end

with is_dependentT {lang} (t : type lang) : bool :=
  match t with
  | Tparam _
  | Tresult_param _
  | Tresult_global _
  | Tresult_unop _ _
  | Tresult_binop _ _ _
  | Tresult_call _ _
  | Tresult_member_call _ _ _
  | Tresult_parenlist _ _ => true
  | Tresult_member _ _ => true
  | Tptr t
  | Tref t
  | Trv_ref t => is_dependentT t
  | Tnum _ _
  | Tchar_ _
  | Tvoid => false
  | Tarray t _
  | Tincomplete_array t => is_dependentT t
  | Tvariable_array t e => is_dependentT t || is_dependentE e
  | Tnamed n
  | Tenum n => is_dependentN n
  | Tfunction ft => function_type.existsb is_dependentT ft
  | Tbool => false
  | Tmember_pointer gn t => is_dependentN gn || is_dependentT t
  | Tfloat_ _ => false
  | Tqualified _ t => is_dependentT t
  | Tnullptr
  | Tarch _ _ => false
  | Tdecltype e => is_dependentE e
  | Tunsupported _ => false
  end

with is_dependentE {lang} (e : Expr lang) : bool :=
  match e with
  | Eparam _
  | Eunresolved_global _
  | Eunresolved_unop _ _
  | Eunresolved_binop _ _ _
  | Eunresolved_call _ _
  | Eunresolved_member_call _ _ _
  | Eunresolved_parenlist _ _
  | Eunresolved_member _ _ => true
  | Evar _ t => is_dependentT t
  | Eenum_const n _ => is_dependentN n
  | Eglobal n t => is_dependentN n || is_dependentT t
  | Echar _ t
  | Estring _ t
  | Eint _ t => is_dependentT t
  | Ebool _ => false
  | Eunop _ e t => is_dependentE e || is_dependentT t
  | Ebinop _ e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Ederef e t => is_dependentE e || is_dependentT t
  | Eaddrof e => is_dependentE e
  | Eassign e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Eassign_op _ e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Epreinc e t => is_dependentE e || is_dependentT t
  | Epostinc e t => is_dependentE e || is_dependentT t
  | Epredec e t => is_dependentE e || is_dependentT t
  | Epostdec e t => is_dependentE e || is_dependentT t
  | Eseqand e1 e2 => is_dependentE e1 || is_dependentE e2
  | Eseqor e1 e2 => is_dependentE e1 || is_dependentE e2
  | Ecomma e1 e2 => is_dependentE e1 || is_dependentE e2
  | Ecall e es => is_dependentE e || existsb is_dependentE es
  | Ecast c e _ t => Cast.existsb is_dependentT is_dependentN is_dependentT c || is_dependentE e || is_dependentT t
  | Emember e _ _ t => is_dependentE e || is_dependentT t
  | Emember_call m e es => MethodRef.existsb is_dependentN is_dependentT is_dependentE m || is_dependentE e || existsb is_dependentE es
  | Eoperator_call _ i es => operator_impl.existsb is_dependentN is_dependentT i || existsb is_dependentE es
  | Esubscript e1 e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Esizeof te t
  | Ealignof te t => sum.existsb is_dependentT is_dependentE te || is_dependentT t
  | Eoffsetof gn _ t => is_dependentT gn || is_dependentT t
  | Econstructor n es t => is_dependentN n || existsb is_dependentE es || is_dependentT t
  | Eimplicit e => is_dependentE e
  | Eimplicit_init t => is_dependentT t
  | Eif e1 e2 e3 _ t => is_dependentE e1 || is_dependentE e2 || is_dependentE e3 || is_dependentT t
  | Eif2 _ e1 e2 e3 e4 _ t => is_dependentE e1 || is_dependentE e2 || is_dependentE e3 || is_dependentE e4 || is_dependentT t
  | Ethis t => is_dependentT t
  | Enull => false
  | Einitlist es eo t => existsb is_dependentE es || option.existsb is_dependentE eo || is_dependentT t
  | Enew p es _ t e1 e2 => is_dependentN p.1 || is_dependentT p.2 || existsb is_dependentE es || is_dependentT t || option.existsb is_dependentE e1 || option.existsb is_dependentE e2
  | Edelete _ p e t => is_dependentN p.1 || is_dependentT p.2 || is_dependentE e || is_dependentT t
  | Eandclean e => is_dependentE e
  | Ematerialize_temp e _ => is_dependentE e
  | Eatomic _ es t => existsb is_dependentE es || is_dependentT t
  | Eva_arg e t => is_dependentE e || is_dependentT t
  | Epseudo_destructor _ t e => is_dependentT t || is_dependentE e
  | Earrayloop_init _ e1 _ _ e2 t => is_dependentE e1 || is_dependentE e2 || is_dependentT t
  | Earrayloop_index _ t => is_dependentT t
  | Eopaque_ref _ _ t => is_dependentT t
  | Eunsupported _ _ t => is_dependentT t
  end.
