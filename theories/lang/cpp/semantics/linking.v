(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import stdpp.fin_maps.
Require Import bedrock.lang.prelude.base.
Require Import bedrock.lang.prelude.exn.
Require Import bedrock.lang.cpp.ast.

(** * Linking translation units *)
(** Thanks to the one-definition rule (ODR), linking is pretty simple.
We don't have to alpha-vary code, for example, when linking two copies
of an inlined function.

The linker [link] links a pair of translation units, presupposing they
are well-formed. It checks the ODR and computes either the linked
translation unit or a reason they can't be linked.

See the ODR:

- https://eel.is/c++draft/basic.def.odr
- https://en.cppreference.com/w/cpp/language/definition *)


(** [link_whence] and [link_err] are provide context to humans when
    linking fails. *)
Inductive link_whence :=
| Wroot
(** Entries in the symbol table *)
| Wsymbol (w : link_whence) (name : globname)
| Wvar (w : link_whence)
| Wfunction (w : link_whence)
| Wmethod (w : link_whence)
| Wctor (w : link_whence)
| Wdtor (w : link_whence)
(** Entries in the type table *)
| Wglobal (w : link_whence) (name : globname)
| Wunion (w : link_whence)
| Wstruct (w : link_whence)
| Wenum (w : link_whence)
| Wconstant (w : link_whence)
| Wtypedef (w : link_whence)
(** Member of a struct or union *)
| Wmember (w : link_whence) (name : obj_name)
.
Variant link_err :=
| Esyntactic_mismatch (w : link_whence) {A} (a b : A)
  (** Attempt to link objects of different syntactic categories.
      Example: [a] an [Ovar], [b] an [Ofunction] *)
| Emultiply_defined (w : link_whence) {A : Type} (a b : A)
  (** [a], [b] should not both be defined, but are *)
| Emultiply_initialized (w : link_whence) {A} (a b : A)
  (** [a], [b] should not both have initializers, but do *)
| Enot_equal (w : link_whence) {A} (a b : A)
  (** [a], [b] do not agree, but should *)
| Elength_mismatch (w : link_whence) {A} (a b : list A)
  (** [a], [b] do not have the same length, but should *)
.

Local Notation M := (exn link_err) (only parsing).
Local Notation Link A := (link_whence → A → A → M A) (only parsing).

Definition require_eq `{EqDecision A} (w : link_whence) (a b : A) : M unit :=
  if decide (a = b) then Ret () else Exn (Enot_equal w a b).

Definition link_eq `{EqDecision A} : Link A := λ w a b,
  _ ← require_eq w a b; Ret a.

(** The draft standard says "After all adjustments of types (during
    which typedefs are replaced by their definitions), the types
    specified by all declarations referring to a given variable or
    function shall be identical, except that declarations for an array
    object can specify array types that differ by the presence or
    absence of a major array bound".
    (https://eel.is/c++draft/basic.link#11).

    We therefore use [link_var_type] to compare the types of
    (top-level) variable declarations/definitions, and [link_type]
    everywhere else. *)
Definition link_type : Link type := λ w a b,
  _ ← require_eq w (normalize_type a) (normalize_type b); Ret a.
Definition link_var_type : Link type := λ w a b,
  match a, b with
  | Tarray ty1 n, Tptr ty2
  | Tptr ty2, Tarray ty1 n => ty ← link_type w ty1 ty2; Ret (Tarray ty n)
  | _, _ => link_type w a b
  end.

(** An abstraction binding some typed identifiers in an optional body.
    The types and bodies must always match up. Bodies must be _equal_
    rather than alpha equivalent per the ODR's requirement that
    definitions "consist of the same sequence of tokens". The bound
    identifiers must match up when there's a body. *)
Local Notation Code A := (list (ident * type) * option A)%type (only parsing).
Definition link_code `{EqDecision A} (inline : bool) : Link (Code A) := λ w a b,
  let check_types : M unit :=
    require_eq w (normalize_type <$> a.1.*2) (normalize_type <$> b.1.*2)
  in
  let maybe_Ret : Code A → M (Code A) := λ x, _ ← check_types; Ret x in
  match a.2, b.2 with
  | None, _ => maybe_Ret b
  | _, None => maybe_Ret a
  | Some a_code, Some b_code =>
    if inline then
      _ ← check_types;
      _ ← require_eq w a_code b_code;
      Ret a
    else Exn (Emultiply_defined w a b)
  end.
Definition link_closed_code `{EqDecision A} (inline : bool) : Link (option A) :=
  λ w a b, code ← link_code inline w (nil, a) (nil, b); Ret code.2.

Local Notation link_cc := (link_eq (A:=calling_conv)) (only parsing).
Definition link_func : Link Func := λ w a b,
  ret ← link_type w a.(f_return) b.(f_return);
  cc  ← link_cc   w a.(f_cc)     b.(f_cc);
  (** PDS: we want agreement on an [f_inline : bool] from the AST. The
      ODR treats inlined functions differently from non-inlined
      functions. *)
  let inline := false in
  code ← link_code inline w
    (a.(f_params), a.(f_body))
    (b.(f_params), b.(f_body));
  Ret (Build_Func ret code.1 cc code.2).

Local Notation link_class := (link_eq (A:=globname)) (only parsing).
Local Notation link_qual := (link_eq (A:=type_qualifiers)) (only parsing).
Definition link_method : Link Method := λ w a b,
  ret       ← link_type  w a.(m_return)    b.(m_return);
  class     ← link_class w a.(m_class)     b.(m_class);
  this_qual ← link_qual  w a.(m_this_qual) b.(m_this_qual);
  cc        ← link_cc    w a.(m_cc)        b.(m_cc);
  (** PDS: we want [m_inline : bool] from the AST. *)
  let inline := false in
  code ← link_code inline w
    (a.(m_params), a.(m_body))
    (b.(m_params), b.(m_body));
  Ret (Build_Method ret class this_qual code.1 cc code.2).

Definition link_ctor : Link Ctor := λ w a b,
  class ← link_class w a.(c_class) b.(c_class);
  cc    ← link_cc    w a.(c_cc)    b.(c_cc);
  (** PDS: we want [c_inline : bool] from the AST. *)
  let inline := false in
  code ← link_code inline w
    (a.(c_params), a.(c_body))
    (b.(c_params), b.(c_body));
  Ret (Build_Ctor class code.1 cc code.2).

Definition link_dtor : Link Dtor := λ w a b,
  class ← link_class w a.(d_class) b.(d_class);
  cc    ← link_cc    w a.(d_cc)    b.(d_cc);
  (** PDS: we want [d_inline : bool] from the AST. *)
  let inline := false in
  body ← link_closed_code inline w a.(d_body) b.(d_body);
  Ret (Build_Dtor class cc body).

Definition link_obj_value : Link ObjValue := λ w a b,
  match a, b with
  | Ovar ty1 e1, Ovar ty2 e2 =>
    ty ← link_var_type w ty1 ty2;
    (** Non-inline because a global can only be initialized once. *)
    (** PDS: Link to the standard *)
    init ← link_closed_code false w e1 e2;
    Ret (Ovar ty init)
  | Ofunction f1, Ofunction f2 =>
    f ← link_func (Wfunction w) f1 f2; Ret (Ofunction f)
  | Omethod m1, Omethod m2 =>
    m ← link_method (Wmethod w) m1 m2; Ret (Omethod m)
  | Oconstructor c1, Oconstructor c2 =>
    c ← link_ctor (Wctor w) c1 c2; Ret (Oconstructor c)
  | Odestructor d1, Odestructor d2 =>
    d ← link_dtor (Wdtor w) d1 d2; Ret (Odestructor d)
  | _, _ => Exn (Esyntactic_mismatch w a b)
  end.

(** Unfortunately, neither stdpp nor the Coq standard library offers
    an operation "[union_with] with keys". *)
Definition link_table {A} (W : link_whence → bs → link_whence) (link : Link A) :
    Link (avl.IM.t A) := λ w a b,
  both ← map_fold (λ name va tblM,
    match b !! name with
    | None => tblM
    | Some vb => tbl ← tblM; v ← link (W w name) va vb; Ret (<[name := v]> tbl)
    end) (Ret ∅) a;
  Ret (a ∖ b ∪ both ∪ b ∖ a).

Definition link_symbol_table : Link symbol_table :=
  link_table Wsymbol link_obj_value.

Definition link_list {A} (link : Link A) : Link (list A) := λ w a b,
  if decide (length a = length b) then
    foldr (λ '(x, y) lM, z ← link w x y; l ← lM; Ret (z :: l)) (Ret nil) (zip a b)
  else Exn (Elength_mismatch w a b).

(** Member of a struct or union *)
Local Notation Member := (ident * type * option Expr * LayoutInfo)%type
  (only parsing).
Local Notation link_ident := (link_eq (A:=ident)) (only parsing).
Local Notation link_layout_info := (link_eq (A:=LayoutInfo)) (only parsing).
(** The [true] here means "treat member initializers like inlined
    functions": if both members have an initializer, they must be
    equal. *)
Local Notation link_default_member_initializer := (link_closed_code (A:=Expr) true)
  (only parsing).
Definition link_member : Link Member := λ w a b,
  id ← link_ident w a.1.1.1 b.1.1.1; let w := Wmember w id in
  ty ← link_type w a.1.1.2 b.1.1.2;
  init ← link_default_member_initializer w a.1.2 b.1.2;
  li ← link_layout_info w a.2 b.2;
  Ret (id, ty, init, li).
Definition link_members : Link (list Member) := link_list link_member.

Local Notation link_N := (link_eq (A:=N)) (only parsing).
Definition link_union : Link translation_unit.Union := λ w a b,
  fields ← link_members w a.(u_fields) b.(u_fields);
  size ← link_N w a.(u_size) b.(u_size);
  (** "At most one variant member of a union may have a default member
      initializer."

      - https://eel.is/c++draft/class.union
      - https://en.cppreference.com/w/cpp/language/union *)
  if filter (λ f, is_Some f.1.2) fields is f1 :: f2 :: _
  then Exn (Emultiply_initialized w f1 f2)
  else Ret (Build_Union fields size).

(** PDS: Structure linking deserves attention. I don't understand
    virtual base classes, virtuals members, overrides, and virtual
    destructors. *)
Notation link_bases := (link_eq (A:=(list (globname * LayoutInfo)))) (only parsing).
(** PDS: Deserves attention. [Unspecified] seems to be our invention. *)
Definition link_layout_type : Link LayoutType := λ w a b,
  match a, b with
  | _, Unspecified => Ret a
  | Unspecified, _ => Ret b
  | _, _ => link_eq w a b
  end.
Notation link_virtuals := (link_eq (A:=(list (obj_name * option obj_name))))
  (only parsing).
Notation link_overrides := (link_eq (A:=(list (obj_name * obj_name))))
  (only parsing).
Notation link_virtual_dtor := (link_eq (A:=(option obj_name))) (only parsing).
Definition link_struct : Link Struct := λ w a b,
  bases ← link_bases w a.(s_bases) b.(s_bases);
  fields ← link_members w a.(s_fields) b.(s_fields);
  layout ← link_layout_type w a.(s_layout) b.(s_layout);
  size ← link_N w a.(s_size) b.(s_size);
  virtuals ← link_virtuals w a.(s_virtuals) b.(s_virtuals);
  overrides ← link_overrides w a.(s_overrides) b.(s_overrides);
  virtual_dtor ← link_virtual_dtor w a.(s_virtual_dtor) b.(s_virtual_dtor);
  Ret (Build_Struct bases fields layout size virtuals overrides virtual_dtor).

Local Notation link_enumerator_list := (link_eq (A:=list ident)) (only parsing).
Definition link_glob_decl : Link GlobDecl := λ w a b,
  match a, b with
  (** Types that are incomplete in one translation unit may be
      complete in the other. *)
  | Gtype, _ => Ret b
  | _, Gtype => Ret a

  | Gunion u1, Gunion u2 => u ← link_union (Wunion w) u1 u2; Ret (Gunion u)

  | Gstruct s1, Gstruct s2 => s ← link_struct (Wstruct w) s1 s2; Ret (Gstruct s)

  | Genum ty1 ids1, Genum ty2 ids2 =>
    let w := Wenum w in
    (** PDS: Check the standard *)
    ty ← link_type w ty1 ty2;
    ids ← link_enumerator_list w ids1 ids2;
    Ret (Genum ty ids)

  (** We put C++ constant expressions in the type table rather than
      the symbol table because they don't represent symbols. Unlike an
      [Ovar], you can't take the address of a [Gconstant]. *)
  | Gconstant ty1 init1, Gconstant ty2 init2 =>
    let w := Wconstant w in
    ty ← link_type w ty1 ty2;
    (** Variables declared [constexpr] are implicitly inlined. See

        - https://eel.is/c++draft/dcl.constexpr#1
        - https://en.cppreference.com/w/cpp/language/inline *)
    init ← link_closed_code true w init1 init2;
    Ret (Gconstant ty init)

  | Gtypedef ty1, Gtypedef ty2 =>
    (** Typedefs are declarations, not definitions, so the ODR does
        not apply here. PDS: However, XXX does. *)
    ty ← link_type (Wtypedef w) ty1 ty2; Ret (Gtypedef ty)

  | _, _ => Exn (Esyntactic_mismatch w a b)
  end.

Definition link_type_table : Link type_table :=
  link_table Wglobal link_glob_decl.

Local Notation link_endian := (link_eq (A:=endian)) (only parsing).
Definition link_translation_unit : Link translation_unit := λ w a b,
  symbols ← link_symbol_table w a.(symbols) b.(symbols);
  globals ← link_type_table w a.(globals) b.(globals);
  byte_order ← link_endian w a.(byte_order) b.(byte_order);
  Ret (Build_translation_unit symbols globals byte_order).

Definition link : translation_unit → translation_unit → M translation_unit :=
  link_translation_unit Wroot.

(** * Strawman theory *)
Require Import bedrock.lang.cpp.semantics.sub_module.
Require Import bedrock.lang.cpp.semantics.values.
Module toy_theory.
  (** PDS: I think we want the following theory. Note that [link]
      cannot be commutative because we permit bound names to vary when
      functions are merely declared (as opposed to defined). Less
      important (because it could be avoided), commutativity also
      fails due to the way types are computed.

      More important than either of these static bars to commutativity
      is that we will eventually support initializers, and the natural
      initializer for [link a b] sequences [a]'s initializer before
      [b]'s. This deserves a caveat (PDS): I've not checked the
      standard to see if it has anything to say about initialization
      and linking---it may well be "unnatural". *)
  Section link.
    (** The following assumptions, if proved, imply that the
        [genv_compat] side-condition in linking lemmas aren't vacuous
        when the translation units can be linked. *)
    Context (link_sub_module_l : ∀ m1 m2 m, link m1 m2 = Ret m → sub_module m1 m).
    Context (link_sub_module_r : ∀ m1 m2 m, link m1 m2 = Ret m → sub_module m2 m).

    Lemma link_genv_compat m1 m2 m : link m1 m2 = Ret m → ∃ σ, m1 ⊧ σ ∧ m2 ⊧ σ.
    Proof using link_sub_module_l link_sub_module_r.
      intros. exists (Build_genv m (λ _, None) 8). split; constructor; simpl.
      exact: link_sub_module_l. exact: link_sub_module_r.
    Qed.
  End link.

  (** This is a strawman only *)
  Section link_genv.
    (** PDS: The following forgetful linker (inadequately) lifts
        linking of translation units to linking of [genv]s. It is not
        adequate for composing proofs via [genv_leq] because it
        forgets the addresses of globals. This is due to the fact that
        [glob_addr] is a Coq function. We could avoid this limitation
        by (i) switching to [glob_addr : IM.t ptr] and (ii) using
        [link_table]. *)
    Definition link_genv_forgetful : Link genv := λ w a b,
      tu ← link_translation_unit w a.(genv_tu) b.(genv_tu);
      pointer_size ← link_N w a.(pointer_size) b.(pointer_size);
      Ret (Build_genv tu (λ _, None) pointer_size).

    Definition genv_link : genv → genv → M genv :=
      link_genv_forgetful Wroot.

    (** PDS: These aren't provable ATM because [genv_link] is forgetful *)
    Lemma genv_link_leq_l σ1 σ2 σ : genv_link σ1 σ2 = Ret σ → genv_leq σ1 σ.
    Abort.
    Lemma genv_link_leq_r σ1 σ2 σ : genv_link σ1 σ2 = Ret σ → genv_leq σ2 σ.
    Abort.
    (** A trivial observation: if you can link [genv]s, you can link their
        translation units. *)
    Lemma genv_link_link σ1 σ2 σ :
      genv_link σ1 σ2 = Ret σ → link σ1.(genv_tu) σ2.(genv_tu) = Ret σ.(genv_tu).
    Proof.
      rewrite/genv_link/link_genv_forgetful /link.
      case: (link_translation_unit _ _ _)=>//= tu.
      case: (link_N _ _ _)=>//= sz.
      by case=><-/=.
    Qed.
  End link_genv.
End toy_theory.
