(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Export bedrock.lang.cpp.arith.types.
Require Import bedrock.lang.cpp.syntax.names.

Set Primitive Projections.

Section Sequence.
  Context {T : Type}.
  Class Sequence : Type :=
  { E : Type
  ; to_list : T -> list E
  ; from_list : list E -> T
  ; from_to x : to_list (from_list x) = x
  ; to_from x : from_list (to_list x) = x
  }.

  Context {s : Sequence}.
  Definition slength (l : T) : nat := length (to_list l).
  Definition sForall (P : E -> Prop) (l : T) : Prop := Forall P (to_list l).
  Definition smap (f : E -> E) (l : T) : T := from_list (List.map f (to_list l)).
End Sequence.
Arguments Sequence _ : clear implicits.

(* Type qualifiers *)
Record type_qualifiers : Set :=
{ q_const : bool
; q_volatile : bool }.
Instance qual_eq: EqDecision type_qualifiers.
Proof. solve_decision. Defined.
Instance qual_countable : Countable type_qualifiers.
Proof.
  apply (inj_countable'
    (λ q, (q_const q, q_volatile q))
    (λ q, {| q_const := q.1; q_volatile := q.2 |})).
  abstract (by intros []).
Defined.

Definition merge_tq (a b : type_qualifiers) : type_qualifiers :=
  {| q_const := a.(q_const) || b.(q_const)
   ; q_volatile := a.(q_volatile) || b.(q_volatile)
   |}.

(* Calling conventions are a little bit beyond what is formally blessed by
   C++, but the are necessary for low level code that links with other
   languages.

   From the C++ standard point of view, we view these as opaque symbols with
   no particular meaning. All that matters is that when you call a function,
   that this calling convention matches between the caller and the callee.
   This is what ensures, for example, that when you call a function implemented
   in another language, that you have the appropriate annotations in place.
   For example, if you were calling an OpenCL kernel, then the function would
   have type [Tfunction (cc:=CC_OpenCLKernel) ..], and you would require that
   annotation in your program.
 *)
Variant calling_conv : Set :=
| CC_C
| CC_MsAbi
| CC_RegCall.
Instance calling_conv_inhabited : Inhabited calling_conv := populate CC_C.
Instance calling_conv_eq_dec: EqDecision calling_conv.
Proof. solve_decision. Defined.
Instance calling_conv_countable : Countable calling_conv.
Proof.
  apply (inj_countable'
    (λ cc,
      match cc with
      | CC_C => 0 | CC_MsAbi => 1 | CC_RegCall => 2
      end)
    (λ n,
      match n with
      | 0 => CC_C | 1 => CC_MsAbi | 2 => CC_RegCall
      | _ => CC_C	(** dummy *)
      end)).
  abstract (by intros []).
Defined.

(* in almost all contexts, we are going to use [CC_C], so we're going to make
   that the default. Clients interested in specifying another calling convention
   should write, e.g., [Tfunction (cc:=CC_PreserveAll) ..] to specify the
   calling convention explicitly.
 *)
Existing Class calling_conv.
Existing Instance CC_C.

(** * Unary operators *)
Variant UnOp : Set :=
| Uminus
| Unot
| Ubnot
| Uother (_ : bs).
Instance: EqDecision UnOp.
Proof. solve_decision. Defined.

(** * Binary operators *)
Variant BinOp : Set :=
| Badd
| Band (* & *)
| Bcmp (* <=> *)
| Bdiv (* / *)
| Beq
| Bge
| Bgt
| Ble
| Blt
| Bmul
| Bneq
| Bor  (* | *)
| Bmod
| Bshl
| Bshr
| Bsub
| Bxor (* ^ *)
| Bdotp (* .* *)
| Bdotip (* ->* *)
.
Instance: EqDecision BinOp.
Proof. solve_decision. Defined.

(** * Atomic operations *)
Variant AtomicOp : Set :=
| AO__atomic_load
| AO__atomic_load_n
| AO__atomic_store
| AO__atomic_store_n
| AO__atomic_compare_exchange
| AO__atomic_compare_exchange_n
| AO__atomic_exchange
| AO__atomic_exchange_n
| AO__atomic_fetch_add
| AO__atomic_fetch_sub
| AO__atomic_fetch_and
| AO__atomic_fetch_or
| AO__atomic_fetch_xor
| AO__atomic_fetch_nand
| AO__atomic_add_fetch
| AO__atomic_sub_fetch
| AO__atomic_and_fetch
| AO__atomic_or_fetch
| AO__atomic_xor_fetch
| AO__atomic_nand_fetch
.
Instance: EqDecision AtomicOp.
Proof. solve_decision. Defined.

(** * Builtin functions *)
Variant BuiltinFn : Set :=
| Bin_alloca
| Bin_alloca_with_align
| Bin_expect
| Bin_unreachable
| Bin_trap
| Bin_bswap16
| Bin_bswap32
| Bin_bswap64
| Bin_bswap128
| Bin_bzero
| Bin_ffs
| Bin_ffsl
| Bin_ffsll
| Bin_clz
| Bin_clzl
| Bin_clzll
| Bin_ctz
| Bin_ctzl
| Bin_ctzll
| Bin_popcount
| Bin_popcountl
| Bin_unknown (_ : bs)
| Bin_launder
.
Instance: EqDecision BuiltinFn.
Proof. solve_decision. Defined.

(** * Value Categories *)
Variant ValCat : Set := Lvalue | Prvalue | Xvalue.
Instance: EqDecision ValCat.
Proof. solve_decision. Defined.


Variant call_type : Set := Virtual | Direct.
Instance: EqDecision call_type.
Proof. solve_decision. Defined.

(** * References *)
Variant VarRef : Set :=
| Lname (_ : localname)
| Gname (_ : globname).
Instance: EqDecision VarRef.
Proof. solve_decision. Defined.

(* types *)
Inductive type : Set :=
| Tptr (_ : type)
| Tref (_ : type)
| Trv_ref (_ : type)
| Tint (size : bitsize) (signed : signed)
| Tvoid
| Tarray (_ : type) (_ : N) (* unknown sizes are represented by pointers *)
| Tnamed (_ : globname)
| Tfunction {cc : calling_conv} (_ : type) (_ : tlist)
| Tbool
| Tmember_pointer (_ : globname) (_ : type)
| Tfloat (_ : bitsize)
| Tqualified (_ : type_qualifiers) (_ : type)
| Tnullptr

| Tvar (_ : bs) (* a reference to a type variable *)
| Tspecialize (_ : bs) (_ : talist)

| Tdependent (* a reference to an unnamed type variable *)

(* architecture-specific types; currently unused.
   some Tarch types, like ARM SVE, are "sizeless", hence [option size]. *)
| Tarch (_ : option bitsize) (name : bs)

with tlist : Set :=
| tnil
| tcons (_ : type) (_ : tlist)

with Expr : Set :=
| Econst_ref (_ : VarRef) (_ : type)
  (* ^ these are different because they do not have addresses *)
| Evar     (_ : VarRef) (_ : type)
  (* ^ local and global variable references *)

| Echar    (_ : Z) (_ : type)
| Estring  (_ : bs) (_ : type)
| Eint     (_ : Z) (_ : type)
| Ebool    (_ : bool)
  (* ^ literals *)

| Eunop    (_ : UnOp) (_ : Expr) (_ : type)
| Ebinop   (_ : BinOp) (_ _ : Expr) (_ : type)
 (* ^ note(gmm): overloaded operators are already resolved. so an overloaded
  * operator shows up as a function call, not a `Eunop` or `Ebinop`.
  * this includes the assignment operator for classes.
  *)
| Ederef (_ : Expr) (_ : type) (* XXX type = strip pointer from (type_of e) *)
| Eaddrof (_ : Expr)
| Eassign (e1 _ : Expr) (_ : type) (* type = type_of e1, if not dependent *)
| Eassign_op (_ : BinOp) (e1 _ : Expr) (_ : type) (* type = type_of e1, if not dependent *)
  (* ^ these are specialized because they are common *)

| Epreinc (_ : Expr) (_ : type)
| Epostinc (_ : Expr) (_ : type)
| Epredec (_ : Expr) (_ : type)
| Epostdec (_ : Expr) (_ : type)
  (* ^ special unary operators *)

| Eseqand (_ _ : Expr) (* type = Tbool *)
| Eseqor  (_ _ : Expr) (* type = Tbool *)
| Ecomma (vc : ValCat) (e1 e2 : Expr) (* type = type_of e2 *)
  (* ^ these are specialized because they have special control flow semantics *)

| Ecall    (_ : Expr) (_ : celist) (_ : type)
| Ecast    (_ : Cast) (_ : ValCat * Expr) (_ : type)

| Emember  (_ : ValCat) (obj : Expr) (_ : field) (_ : type)
  (* TODO: maybe replace the left branch use [Expr] here? *)
| Emember_call (method : (obj_name * call_type * type) + Expr) (_ : ValCat) (obj : Expr) (_ : celist) (_ : type)
  (* ^ [Emember_call (inl (f, Direct, t)) vc obj ...] is essentially the same as
       [Emember_call (inr (Emember vc obj {| f_name := f ; f_type := t |})) vc obj ...]
       but this doesn't exactly work because member functions are not fields.
   *)

| Esubscript (_ : Expr) (_ : Expr) (_ : type)
| Esize_of (_ : type + Expr) (_ : type)
| Ealign_of (_ : type + Expr) (_ : type)
| Econstructor (_ : globname) (_ : celist) (_ : type)
| Eimplicit (e : Expr) (* type = type_of e *)
| Eimplicit_init (_ : type)
| Eif       (_ _ _ : Expr) (_ : type)

| Ethis (_ : type)
| Enull
| Einitlist (_ : list Expr) (_ : option Expr) (_ : type)

| Enew (new_fn : option (obj_name * type)) (new_args : celist)
       (alloc_ty : type)
       (array_size : option Expr) (init : option Expr) (_ : type)
| Edelete (is_array : bool) (delete_fn : option (obj_name * type)) (arg : Expr)
          (deleted_type : type) (_ : type)

| Eandclean (e : Expr) (* type = type_of e *)
| Ematerialize_temp (e : Expr) (* type = type_of e *)

| Ebuiltin (_ : BuiltinFn) (_ : type)
| Eatomic (_ : AtomicOp) (_ : celist) (_ : type)
| Eva_arg (_ : Expr) (_ : type)
| Epseudo_destructor (_ : type) (_ : Expr) (* type void *)

| Earrayloop_init (oname : N) (src : ValCat * Expr) (level : N) (length : N) (init : Expr) (_ : type)
| Earrayloop_index (level : N) (_ : type)
| Eopaque_ref (name : N) (_ : type)

| Eunresolved_ctor (_ : type) (_ : celist)
| Eunresolved_member (_ : type) (_ : bs) (_ : type)
| Eunresolved_symbol (_ : bs) (_ : type)

(*
  template<typename T, int X>
  int f(T x) {
    Foo<X + 1> blah;
    int a[X];
    x.bar(); // Emember_call (inr (Eunresolved_member ..))
    foo(x); // Ecall (Eunresolved_symbol ..) (x)
            // Ecall (Ecast (function2pointer) (Evar "foo"))
  }

*)

| Eunsupported (_ : bs) (_ : type)

with celist : Set :=
| cenil
| cecons (_ : ValCat) (_ : Expr) (_ : celist)

with Cast : Set :=
| Cdependent (* this doesn't have any semantics *)
| Cbitcast
| Clvaluebitcast
| Cl2r
| Cnoop
| Carray2pointer
| Cfunction2pointer
| Cint2pointer
| Cpointer2int
| Cptr2bool
| Cderived2base
| Cbase2derived
| Cintegral
| Cint2bool
| Cnull2ptr
| Cbuiltin2function
| Cconstructorconversion
| C2void
| Cuser        (conversion_function : obj_name)
| Creinterpret (_ : type)
| Cstatic      (from to : globname)
| Cdynamic     (from to : globname)
| Cconst       (_ : type)

with template_arg : Set :=
| template_type (_ : type)
| template_value (_ : Expr)

with talist : Set :=
| tanil
| tacons (_ : template_arg) (_ : talist)
.
Instance type_inhabited : Inhabited type := populate Tvoid.
#[global] Instance tlist_inhabited : Inhabited tlist := populate tnil.
#[global] Instance talist_inhabited : Inhabited talist := populate tanil.
#[global] Instance celist_inhabited : Inhabited celist := populate cenil.


#[global,program] Instance Seq_talist : Sequence talist :=
{| to_list := fix go a := match a with
                          | tanil => nil
                          | tacons x xs => x :: go xs
                          end
 ; from_list := fix go a := match a with
                            | nil => tanil
                            | x :: xs => tacons x (go xs)
                            end |}.
Next Obligation. induction x; f_equal; eauto. Qed.
Next Obligation. induction x; f_equal; eauto. Qed.
#[global,program] Instance Seq_tlist : Sequence tlist :=
{| to_list := fix go a := match a with
                          | tnil => nil
                          | tcons x xs => x :: go xs
                          end
 ; from_list := fix go a := match a with
                            | nil => tnil
                            | x :: xs => tcons x (go xs)
                            end |}.
Next Obligation. induction x; f_equal; eauto. Qed.
Next Obligation. induction x; f_equal; eauto. Qed.
#[global,program] Instance Seq_celist : Sequence celist :=
{| to_list := fix go a := match a with
                          | cenil => nil
                          | cecons v x xs => (v,x) :: go xs
                          end
 ; from_list := fix go a := match a with
                            | nil => cenil
                            | (v,x) :: xs => cecons v x (go xs)
                            end |}.
Next Obligation. induction x as [|[??]]; f_equal; eauto. Qed.
Next Obligation. induction x; f_equal; eauto. Qed.


Declare Scope tlist_scope.
Bind Scope tlist_scope with tlist.
Notation "[ ]" := tnil (format "[ ]") : tlist_scope.
Notation "[ x ]" := (tcons x tnil) : tlist_scope.
Notation "[ a ; b ; .. ; c ]" := (tcons a (tcons b .. (tcons c tnil) ..)) : tlist_scope.
Infix "::" := tcons : tlist_scope.
Arguments Tfunction {cc} _ _%tlist_scope.
Declare Scope talist_scope.
Bind Scope talist_scope with talist.
Notation "[ ]" := tanil (format "[ ]") : talist_scope.
Notation "[ x ]" := (tacons x tanil) : talist_scope.
Notation "[ a ; b ; .. ; c ]" := (tacons a (tacons b .. (tacons c tanil) ..)) : talist_scope.
Infix "::" := tacons : talist_scope.
Arguments Tspecialize _ _%talist_scope.

(*
Scheme type_rec' := Induction for type Sort Set
  with tlist_rec' := Induction for tlist Sort Set
  with expr_rec' := Induction for Expr Sort Set
  with celist_rec' := Induction for celist Sort Set
  with Cast_rec' := Induction for Cast Sort Set
  with template_arg_rec' := Induction for template_arg Sort Set
  with talist_rec' := Induction for talist Sort Set.
Combined Scheme type_mutind from type_rec', tlist_rec', expr_rec', celist_rec', Cast_rec', template_arg_rec', talist_rec'.
Scheme type_rect' := Induction for type Sort Type
  with tlist_rect' := Induction for tlist Sort Type
  with expr_rect' := Induction for Expr Sort Type
  with celist_rect' := Induction for celist Sort Type
  with Cast_rect' := Induction for Cast Sort Type
  with template_arg_rect' := Induction for template_arg Sort Type
  with talist_rect' := Induction for talist Sort Type.
Scheme type_ind' := Induction for type Sort Prop
  with tlist_ind' := Induction for tlist Sort Prop
  with expr_ind' := Induction for Expr Sort Prop
  with celist_ind' := Induction for celist Sort Prop
  with Cast_ind' := Induction for Cast Sort Prop
  with template_arg_ind' := Induction for template_arg Sort Prop
  with talist_ind' := Induction for talist Sort Prop.
 *)

(*
Section type_ind'.
  Variable P : type -> Prop.

  Hypothesis Tptr_ind' : forall (ty : type),
    P ty -> P (Tptr ty).
  Hypothesis Tref_ind' : forall (ty : type),
    P ty -> P (Tref ty).
  Hypothesis Trv_ref_ind' : forall (ty : type),
    P ty -> P (Trv_ref ty).
  Hypothesis Tint_ind' : forall (size : bitsize) (sign : signed),
    P (Tint size sign).
  Hypothesis Tvoid_ind' : P Tvoid.
  Hypothesis Tarray_ind' : forall (ty : type) (sz : N),
    P ty -> P (Tarray ty sz).
  Hypothesis Tnamed_ind' : forall (name : globname),
    P (Tnamed name).
  Hypothesis Tfunction_ind' : forall {cc : calling_conv} (ty : type) (tys : list type),
    P ty -> Forall P tys -> P (Tfunction ty tys).
  Hypothesis Tbool_ind' : P Tbool.
  Hypothesis Tmember_pointer_ind' : forall (name : globname) (ty : type),
    P ty -> P (Tmember_pointer name ty).
  Hypothesis Tfloat_ind' : forall (size : bitsize),
    P (Tfloat size).
  Hypothesis Tqualified_ind' : forall (q : type_qualifiers) (ty : type),
    P ty -> P (Tqualified q ty).
  Hypothesis Tnullptr_ind' : P Tnullptr.
  Hypothesis Tarch_ind' : forall (osize : option bitsize) (name : bs),
    P (Tarch osize name).
  Hypothesis Tvar_ind' : forall nm, P (Tvar nm).
  Hypothesis Tspecialize_ind' : forall nm ls, Forall (fun ab =>
                                                   match ab with
                                                   | template_type t => P t
                                                   | _ => True
                                                   end) ls -> P (Tspecialize nm ls).

  Fixpoint type_ind' (ty : type) : P ty :=
    match ty with
    | Tptr ty                 => Tptr_ind' ty (type_ind' ty)
    | Tref ty                 => Tref_ind' ty (type_ind' ty)
    | Trv_ref ty              => Trv_ref_ind' ty (type_ind' ty)
    | Tint sz sgn             => Tint_ind' sz sgn
    | Tvoid                   => Tvoid_ind'
    | Tarray ty sz            => Tarray_ind' ty sz (type_ind' ty)
    | Tnamed name             => Tnamed_ind' name
    | Tfunction ty tys        =>
      Tfunction_ind' ty tys (type_ind' ty)
                     (* NOTE: We must use a nested [fix] in order to convince Coq that
                          the elements of [tys] are actually subterms of
                          [Tfunction ty tys]
                      *)
                     ((fix list_tys_ind' (tys : list type) : Forall P tys :=
                         match tys with
                         | []        => List.Forall_nil P
                         | ty :: tys' => List.Forall_cons P ty tys'
                                                        (type_ind' ty) (list_tys_ind' tys')
                         end) tys)
    | Tbool                   => Tbool_ind'
    | Tmember_pointer name ty => Tmember_pointer_ind' name ty (type_ind' ty)
    | Tfloat sz               => Tfloat_ind' sz
    | Tqualified q ty         => Tqualified_ind' q ty (type_ind' ty)
    | Tnullptr                => Tnullptr_ind'
    | Tarch osize name        => Tarch_ind' osize name
    end.
End type_ind'.
*)

Notation Tchar := Tint (only parsing).
(* XXX merge type_eq_dec into type_eq. *)

Definition type_eq_dec : forall (ty1 ty2 : type), { ty1 = ty2 } + { ty1 <> ty2 }.
Proof. (*
  (* rewrite /RelDecision /Decision. *)
  fix IHty1 1.
  rewrite -{1}/(EqDecision type) in IHty1.
  decide equality; try solve_trivial_decision. *)
Admitted. (** TODO *)
Instance type_eq: EqDecision type := type_eq_dec.
Axiom type_countable : Countable type.
#[global] Existing Instance type_countable.
(*
Section type_countable.
  Local Notation BS x      := (GenLeaf (inr x)).
  Local Notation QUAL x    := (GenLeaf (inl (inr x))).
  Local Notation BITSIZE x := (GenLeaf (inl (inl (inr x)))).
  Local Notation SIGNED x  := (GenLeaf (inl (inl (inl (inr x))))).
  Local Notation CC x      := (GenLeaf (inl (inl (inl (inl (inr x)))))).
  Local Notation N x       := (GenLeaf (inl (inl (inl (inl (inl x)))))).
  Global Instance type_countable : Countable type.
  Proof.
    set enc := fix go (t : type) :=
      match t with
      | Tptr t => GenNode 0 [go t]
      | Tref t => GenNode 1 [go t]
      | Trv_ref t => GenNode 2 [go t]
      | Tint sz sgn => GenNode 3 [BITSIZE sz; SIGNED sgn]
      | Tvoid => GenNode 4 []
      | Tarray t n => GenNode 5 [go t; N n]
      | Tnamed gn => GenNode 6 [BS gn]
      | @Tfunction cc ret args => GenNode 7 $ (CC cc) :: go ret :: (go <$> args)
      | Tbool => GenNode 8 []
      | Tmember_pointer gn t => GenNode 9 [BS gn; go t]
      | Tfloat sz => GenNode 10 [BITSIZE sz]
      | Tqualified q t => GenNode 11 [QUAL q; go t]
      | Tnullptr => GenNode 12 []
      | Tarch None gn => GenNode 13 [BS gn]
      | Tarch (Some sz) gn => GenNode 14 [BITSIZE sz; BS gn]
      end.
    set dec := fix go t :=
      match t with
      | GenNode 0 [t] => Tptr (go t)
      | GenNode 1 [t] => Tref (go t)
      | GenNode 2 [t] => Trv_ref (go t)
      | GenNode 3 [BITSIZE sz; SIGNED sgn] => Tint sz sgn
      | GenNode 4 [] => Tvoid
      | GenNode 5 [t; N n] => Tarray (go t) n
      | GenNode 6 [BS gn] => Tnamed gn
      | GenNode 7 (CC cc :: ret :: args) => @Tfunction cc (go ret) (go <$> args)
      | GenNode 8 [] => Tbool
      | GenNode 9 [BS gn; t] => Tmember_pointer gn (go t)
      | GenNode 10 [BITSIZE sz] => Tfloat sz
      | GenNode 11 [QUAL q; t] => Tqualified q (go t)
      | GenNode 12 [] => Tnullptr
      | GenNode 13 [BS gn] => Tarch None gn
      | GenNode 14 [BITSIZE sz; BS gn] => Tarch (Some sz) gn
      | _ => Tvoid	(** dummy *)
      end.
    apply (inj_countable' enc dec). refine (fix go t := _).
    destruct t as [| | | | | | |cc ret args| | | | | |[]]; simpl; f_equal; try done.
    induction args; simpl; f_equal; done.
  Defined.
End type_countable.
*)
Global Instance expr_eq : EqDecision Expr.
Proof. Admitted. (* TODO *)


Notation Tpointer := Tptr (only parsing).
Notation Treference := Tref (only parsing).
Notation Trv_reference := Trv_ref (only parsing).
Notation Tfun := Tfunction (only parsing).
Definition QCV := {| q_const := true ; q_volatile := true |}.
Definition QC := {| q_const := true ; q_volatile := false |}.
Definition QV := {| q_const := false ; q_volatile := true |}.
Definition QM := {| q_const := false ; q_volatile := false |}.

Definition Qconst_volatile : type -> type :=
  Tqualified QCV.
Definition Qconst : type -> type :=
  Tqualified QC.
Definition Qmut_volatile : type -> type :=
  Tqualified QV.
Definition Qmut : type -> type :=
  Tqualified QM.

Section qual_norm.
  Context {A : Type}.
  Variable f : type_qualifiers -> type -> A.

  Fixpoint qual_norm' (q : type_qualifiers) (t : type) : A :=
    match t with
    | Tqualified q' t =>
      qual_norm' (merge_tq q q') t
    | _ =>
      f q t
    end.

  Definition qual_norm : type -> A :=
    qual_norm' {| q_const := false ; q_volatile := false |}.

End qual_norm.

Definition tqualified (q : type_qualifiers) (t : type) : type :=
  match q with
  | {| q_const := false ; q_volatile := false |} => t
  | _ => Tqualified q t
  end.

(** normalization of types
    - compresses adjacent [Tqualified] constructors
    - drops (irrelevant) qualifiers on function arguments and return types
 *)
Fixpoint normalize_type (t : type) : type :=
  let drop_norm :=
      qual_norm (fun _ t => normalize_type t)
  in
  let qual_norm :=
      (* merge adjacent qualifiers and then normalize *)
      qual_norm' (fun q t => tqualified q (normalize_type t))
  in
  match t with
  | Tpointer t => Tpointer (normalize_type t)
  | Treference t => Treference (normalize_type t)
  | Trv_reference t => Trv_reference (normalize_type t)
  | Tarray t n => Tarray (normalize_type t) n
  | @Tfunction cc r args =>
    Tfunction (cc:=cc) (drop_norm r) (normalize_types args)
  | Tmember_pointer gn t => Tmember_pointer gn (normalize_type t)
  | Tqualified q t => qual_norm q t
  | Tint _ _ => t
  | Tbool => t
  | Tvoid => t
  | Tnamed _ => t
  | Tnullptr => t
  | Tfloat _ => t
  | Tarch _ _ => t
  | Tvar _ => t
  | Tspecialize _ _ => t
  end
with normalize_types (t : tlist) : tlist :=
  match t with
  | tnil => tnil
  | tcons t ts => tcons (qual_norm (fun _ t => normalize_type t) t) (normalize_types ts)
  end.

(* TODO port 
Section normalize_type_idempotent.
  Lemma merge_tq_assoc:
    forall q q' q'',
      merge_tq q (merge_tq q' q'') = merge_tq (merge_tq q q') q''.
  Proof. now intros *; rewrite /merge_tq/= !orb_assoc. Qed.

  Fixpoint _drop_norm_idempotent q q' ty {struct ty}:
    qual_norm' (fun _ t => normalize_type t) q (qual_norm' (fun _ t => normalize_type t) q' ty) =
    qual_norm' (fun _ t => normalize_type t) (merge_tq q q') ty
  with _qual_norm_idempotent q ty {struct ty}:
    normalize_type (qual_norm' (fun q t => tqualified q (normalize_type t)) q ty) =
    qual_norm' (fun q t => tqualified q (normalize_type t)) q ty
  with normalize_type_idempotent ty {struct ty}:
    normalize_type (normalize_type ty) = normalize_type ty.
  Proof.
    { (* _drop_norm_involutive *)
      generalize dependent q; generalize dependent q';
        induction ty using type_ind; intros *;
        rewrite /qual_norm/= ?normalize_type_idempotent//.
      - rewrite map_map /qual_norm !IHty /merge_tq/=;
          erewrite map_ext_Forall; eauto; eapply Forall_impl; eauto;
          intros * HForall; simpl in HForall; apply HForall.
      - now rewrite IHty merge_tq_assoc.
    }
    { (* _qual_norm_involutive *)
      intros *; generalize dependent q;
        induction ty using type_ind'; intros *; simpl;
        try solve[destruct q as [[|] [|]]; simpl; now rewrite ?normalize_type_idempotent].
      destruct q as [[|] [|]]; simpl;
        rewrite map_map /qual_norm ?_drop_norm_idempotent /merge_tq/=;
        try solve[erewrite map_ext_Forall; eauto; induction tys;
                  [ now constructor
                  | constructor;
                    [ now apply _drop_norm_idempotent
                    | apply IHtys; now apply Forall_inv_tail in H]]].
    }
    { (* normalize_type_involutive *)
      intros *; induction ty using type_ind'; simpl; rewrite ?IHty; eauto.
      rewrite map_map /qual_norm _drop_norm_idempotent /merge_tq/=.
      erewrite map_ext_Forall; eauto; induction tys;
        [ now constructor
        | constructor;
          [ now apply _drop_norm_idempotent
          | apply IHtys; now apply Forall_inv_tail in H]].
    }
  Qed.
End normalize_type_idempotent.
 *)

Definition decompose_type : type -> type_qualifiers * type :=
  qual_norm (fun q t => (q, t)).


(* types with explicit size information
 *)
Definition T_int8    := Tint W8 Signed.
Definition T_uint8   := Tint W8 Unsigned.
Definition T_int16   := Tint W16 Signed.
Definition T_uint16  := Tint W16 Unsigned.
Definition T_int32   := Tint W32 Signed.
Definition T_uint32  := Tint W32 Unsigned.
Definition T_int64   := Tint W64 Signed.
Definition T_uint64  := Tint W64 Unsigned.
Definition T_int128  := Tint W128 Signed.
Definition T_uint128 := Tint W128 Unsigned.

(* note(gmm): types without explicit size information need to
 * be parameters of the underlying code, otherwise we can't
 * describe the semantics correctly.
 * - cpp2v should probably insert these types.
 *)
(**
https://en.cppreference.com/w/cpp/language/types
The 4 definitions below use the LP64 data model.
LLP64 and LP64 agree except for the [long] type: see
the warning below.
In future, we may want to parametrize by a data model, or
the machine word size.
*)
Definition char_bits : bitsize := W8.
Definition short_bits : bitsize := W16.
Definition int_bits : bitsize := W32.
Definition long_bits : bitsize := W64. (** warning: LLP64 model uses 32 *)
Definition long_long_bits : bitsize := W64.

Definition T_ushort : type := Tint short_bits Unsigned.
Definition T_short : type := Tint short_bits Signed.
Definition T_ulong : type := Tint long_bits Unsigned.
Definition T_long : type := Tint long_bits Signed.
Definition T_ulonglong : type := Tint long_long_bits Unsigned.
Definition T_longlong : type := Tint long_long_bits Signed.
Definition T_uint : type := Tint int_bits Unsigned.
Definition T_int : type := Tint int_bits Signed.

Notation T_schar := (Tchar char_bits Signed) (only parsing).
Notation T_uchar := (Tchar char_bits Unsigned) (only parsing).

