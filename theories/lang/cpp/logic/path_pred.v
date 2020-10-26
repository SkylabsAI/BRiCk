(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import bedrock.lang.prelude.base.

Require Import iris.proofmode.tactics.
From bedrock.lang.cpp Require Import semantics logic.pred ast.
From iris_string_ident Require Import ltac2_string_ident.

Implicit Types (p : ptr).

(* XXX upstream. *)
Parameter invalid_ptr : ptr.
Axiom invalid_invalid_ptr_1 : forall `{has_cpp : cpp_logic}, valid_ptr invalid_ptr |-- False.

Notation raw_ptr_offset := (option Z).
(* Inductive raw_ptr_offset := InvRawO | RawO (z : Z). *)
Definition raw_offset_ptr_ (r : raw_ptr_offset) (p : ptr) : ptr :=
  default invalid_ptr (flip offset_ptr_ p <$> r).
Arguments raw_offset_ptr_ !_ /.

Axiom offset_invalid_ptr : forall z,
  offset_ptr_ z invalid_ptr = invalid_ptr.
Lemma raw_offset_invalid_ptr r :
  raw_offset_ptr_ r invalid_ptr = invalid_ptr.
Proof. case: r => //= z. exact: offset_invalid_ptr. Qed.

Record Loc `{has_cpp : cpp_logic} : Type := MkLoc
  { _loc_eval : ptr
  ; _valid_loc : mpred
  ; _loc_eval_valid : _valid_loc |-- valid_ptr _loc_eval
  ; _valid_loc_persist : Persistent _valid_loc
  ; _valid_loc_affine : Affine _valid_loc
  ; _valid_loc_timeless : Timeless _valid_loc
  }.
Arguments MkLoc {_ _} _ _%I _ {_ _ _}.
Existing Instances _valid_loc_persist _valid_loc_affine _valid_loc_timeless.

(* TODO: We're exposing actual offsets, so this whole thing must be hidden.
Worse, _offset_eval is the only real semantics.
*)
Record Offset `{has_cpp : cpp_logic} : Type := MkOffset
  { _offset_eval : raw_ptr_offset
  ; _valid_offset : ptr -> mpred
  ; _offset_eval_valid p : _valid_offset p |-- valid_ptr p -* valid_ptr (raw_offset_ptr_ _offset_eval p)
  ; _valid_offset_persist p : Persistent (_valid_offset p)
  ; _valid_offset_affine p : Affine (_valid_offset p)
  ; _valid_offset_timeless p : Timeless (_valid_offset p)
  }.
Arguments MkOffset {_ _} _ _%I _ {_ _ _}.

Existing Instances _valid_offset_persist _valid_offset_affine _valid_offset_timeless.
Definition _location `{cpp_logic} (l : Loc) (p : ptr) : mpred :=
  [| p = _loc_eval l |] ** _valid_loc l.
Arguments _location {_ _} !_ _ /.

Section with_Σ.
  Context `{has_cpp : cpp_logic}.

  Implicit Types (l : Loc) (o : Offset).
  (* locations represent C++ computations that produce an address.
   *)
  (* XXX seal *)

  Lemma _loc_unique l p1 p2 : _location l p1 ** _location l p2 |-- [| p1 = p2 |].
  Proof. rewrite /_location. by iIntros "[[-> _] [-> _]]". Qed.
  Lemma _loc_valid l p1: _location l p1 |-- valid_ptr p1.
  Proof. rewrite /_location /= _loc_eval_valid. iIntros "[-> $]". Qed.
  Global Instance _loc_persist l p: Persistent (_location l p) := _.
  Global Instance _loc_affine l p : Affine (_location l p) := _.
  Global Instance _loc_timeless l p: Timeless (_location l p) := _.

  Definition _offset o p1 p2 : mpred :=
    [| p2 = raw_offset_ptr_ (_offset_eval o) p1 |] ** _valid_offset o p1.
  Lemma _off_functional o p p1 p2: _offset o p p1 ** _offset o p p2 |-- [| p1 = p2 |].
  Proof. rewrite /_offset. by iIntros "[[-> _] [-> _]]". Qed.

  Lemma _off_valid o p1 p2 : valid_ptr p1 ** _offset o p1 p2 |-- valid_ptr p2.
  Proof.
    rewrite /_offset; iIntros "[#VP1 [-> #VO]]".
    by iApply (_offset_eval_valid with "VO VP1").
  Qed.

  Global Instance _off_persist o p1 p2: Persistent (_offset o p1 p2) := _.
  Global Instance _off_affine o p1 p2: Affine (_offset o p1 p2) := _.
  Global Instance _off_timeless o p1 p2: Timeless (_offset o p1 p2) := _.

  Global Instance Loc_Equiv : Equiv Loc :=
    fun l1 l2 => _loc_eval l1 = _loc_eval l2 /\ (_valid_loc l1 -|- _valid_loc l2).

  Global Instance Loc_Equivalence : Equivalence (≡@{Loc}).
  Proof.
    split.
    - done.
    - do 3 red. intros * [??]. by split; symmetry.
    - do 3 red. intros * [??] [??]. by split; etrans.
  Qed.
  Global Instance _loc_eval_proper : Proper ((≡) ==> (=)) _loc_eval.
  Proof. solve_proper. Qed.
  Global Instance _valid_loc_proper : Proper ((≡) ==> (≡)) _valid_loc.
  Proof. solve_proper. Qed.

  Global Instance _location_proper : Proper ((≡) ==> eq ==> (⊣⊢)) _location.
  Proof. rewrite /_location. intros ?? E ?? ->. by rewrite E. Qed.
  Global Instance _location_mono : Proper ((≡) ==> eq ==> (⊢)) _location.
  Proof. intros l1 l2 HL p1 p2 ->. by rewrite HL. Qed.
  Global Instance _location_flip_mono : Proper ((≡) ==> eq ==> flip (⊢)) _location.
  Proof. intros l1 l2 HL p1 p2 ->. by rewrite -HL. Qed.

  (* [mpred] implication between [Loc] *)
  Definition Loc_impl (l1 l2 : Loc) : mpred :=
    [| _loc_eval l1 = _loc_eval l2 |] ** □ (_valid_loc l1 -* _valid_loc l2).

  Global Instance Loc_impl_proper : Proper ((≡) ==> (≡) ==> (≡)) Loc_impl.
  Proof. rewrite /Loc_impl => x y Heq ??->. by rewrite Heq. Qed.
  Global Instance Loc_impl_persistent l1 l2 : Persistent (Loc_impl l1 l2).
  Proof. apply _. Qed.
  Global Instance Loc_impl_affine l1 l2 : Affine (Loc_impl l1 l2).
  Proof. apply _. Qed.
  Global Instance Loc_impl_timeless l1 l2 : Timeless (Loc_impl l1 l2).
  Proof. apply _. Qed.

  Definition Loc_impl_location l1 l2 p :
    Loc_impl l1 l2 |-- _location l1 p -* _location l2 p.
  Proof. rewrite /_location. iIntros "[-> #H] [$ ?]". by iApply "H". Qed.

  (* [mpred] equivalence of [Loc] *)
  Definition Loc_equiv (l1 l2 : Loc) : mpred :=
    [| _loc_eval l1 = _loc_eval l2 |] ** □ (_valid_loc l1 ∗-∗ _valid_loc l2).

  Global Instance Loc_equiv_proper : Proper ((≡) ==> (≡) ==> (≡)) Loc_equiv.
  Proof. rewrite /Loc_equiv => x y Heq ??->. by rewrite Heq. Qed.
  Global Instance Loc_equiv_persistent l1 l2 : Persistent (Loc_equiv l1 l2).
  Proof. apply _. Qed.
  Global Instance Loc_equiv_affine l1 l2 : Affine (Loc_equiv l1 l2).
  Proof. apply _. Qed.
  Global Instance Loc_equiv_timeless l1 l2 : Timeless (Loc_equiv l1 l2).
  Proof. apply _. Qed.

  Lemma Loc_equiv_impl l1 l2 :
    Loc_equiv l1 l2 -|- Loc_impl l1 l2 ** Loc_impl l2 l1.
  Proof.
    rewrite /Loc_equiv/Loc_impl; split'.
    - by iIntros "[-> #[$ $]] !%".
    - by iIntros "[[-> #$] [_ #$]]".
  Qed.

  Lemma Loc_equiv_refl l : |-- Loc_equiv l l.
  Proof. iSplit => //. iIntros "!>". by iApply bi.wand_iff_refl. Qed.
  Lemma Loc_equiv_sym l1 l2 : Loc_equiv l1 l2 |-- Loc_equiv l2 l1.
  Proof. rewrite /Loc_equiv. by iIntros "[-> #[$$]]". Qed.
  Lemma Loc_equiv_trans l1 l2 l3 :
    Loc_equiv l1 l2 |-- Loc_equiv l2 l3 -* Loc_equiv l1 l3.
  Proof.
    rewrite /Loc_equiv. iIntros "[-> #[H12 H21]] [-> #[H23 H32]]".
    iSplit; first done.
    iIntros "!>"; iSplit; iIntros "#H".
    iApply ("H23" with "(H12 H)").
    iApply ("H21" with "(H32 H)").
  Qed.

  (** absolute locations *)
  Lemma invalid_invalid_ptr : valid_ptr invalid_ptr -|- False.
  Proof. split'. apply invalid_invalid_ptr_1. iIntros "[]". Qed.

  Program Definition invalidL : Loc := MkLoc invalid_ptr lfalse _.
  Next Obligation. by rewrite invalid_invalid_ptr. Qed.

  Program Definition _eq_def (p : ptr) : Loc := MkLoc p (valid_ptr p) _.
  Next Obligation. done. Qed.
  Definition _eq_aux : seal (@_eq_def). Proof. by eexists. Qed.
  Definition _eq := _eq_aux.(unseal).
  Definition _eq_eq : @_eq = _ := _eq_aux.(seal_eq).

  Definition _eqv (a : val) : Loc :=
    match a with
    | Vptr p => _eq p
    | _ => invalidL
    end.

  Lemma _eqv_eq : forall p, _eqv (Vptr p) = _eq p.
  Proof. reflexivity. Qed.

  Definition _global_def (resolve : genv) (x : obj_name) : Loc :=
    match glob_addr resolve x with
    | Some p => _eq p
    | _ => invalidL
    end.
  Definition _global_aux : seal (@_global_def). Proof. by eexists. Qed.
  Definition _global := _global_aux.(unseal).
  Definition _global_eq : @_global = _ := _global_aux.(seal_eq).

  Definition _local (ρ : region) (b : ident) : Loc :=
    match get_location ρ b with
    | Some p => _eq p
    | _ => invalidL
    end.

  Definition _this (ρ : region) : Loc :=
    match get_this ρ with
    | Some p => _eq p
    | _ => invalidL
    end.

  Definition _result (ρ : region) : Loc :=
    match get_result ρ with
    | Some p => _eq p
    | _ => invalidL
    end.

  (** [addr_of]: [addr_of l p] says that pointer [p] "matches" location [l]. *)
  Definition addr_of_def (a : Loc) (b : ptr) : mpred :=
    _location a b.
  Definition addr_of_aux : seal (@addr_of_def). Proof. by eexists. Qed.
  Definition addr_of := addr_of_aux.(unseal).
  Definition addr_of_eq : @addr_of = _ := addr_of_aux.(seal_eq).
  Arguments addr_of : simpl never.
  Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

  Global Instance addr_of_proper : Proper ((≡) ==> eq ==> (≡)) addr_of.
  Proof. rewrite addr_of_eq. solve_proper. Qed.
  Global Instance addr_of_mono : Proper ((≡) ==> eq ==> (⊢)) addr_of.
  Proof. rewrite addr_of_eq. solve_proper. Qed.
  Global Instance addr_of_flip_mono : Proper ((≡) ==> eq ==> flip (⊢)) addr_of.
  Proof. rewrite addr_of_eq=>l1 l2 HL p1 p2->/=. by rewrite HL. Qed.

  Global Instance addr_of_persistent : Persistent (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.
  Global Instance addr_of_affine : Affine (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.
  Global Instance addr_of_timeless : Timeless (addr_of o l).
  Proof. rewrite addr_of_eq. apply _. Qed.

  Lemma addr_of_precise : forall a b c,
      addr_of a b ** addr_of a c |-- [| b = c |].
  Proof.
    intros.
    rewrite addr_of_eq /addr_of_def.
    iIntros "[#A #B]".
    iFrame "#".
    iDestruct (_loc_unique with "[A B]") as %H; [ | eauto ]; eauto.
  Qed.

  Lemma addr_of_Loc_eq l p : l &~ p |-- Loc_equiv l (_eq p).
  Proof.
    rewrite /Loc_equiv addr_of_eq /addr_of_def /_location.
    rewrite _eq_eq /_eq_def /=.
    iIntros "[-> #L]". iSplit; first done. iIntros "!>".
    iSplit; iIntros "H"; last done.
    by iApply _loc_eval_valid.
  Qed.

  Lemma addr_of_Loc_impl : forall l p, l &~ p |-- Loc_impl l (_eq p).
  Proof. intros. by rewrite addr_of_Loc_eq Loc_equiv_impl bi.sep_elim_l. Qed.

  (** [valid_loc]
      - same as [addr_of] except that it hides the existential quantifier
   *)
  Definition valid_loc_def (l : Loc) : mpred := Exists p, addr_of l p.
  Definition valid_loc_aux : seal (@valid_loc_def). Proof. by eexists. Qed.
  Definition valid_loc := valid_loc_aux.(unseal).
  Definition valid_loc_eq : valid_loc = @valid_loc_def := valid_loc_aux.(seal_eq).
  Lemma valid_loc_equiv l : valid_loc l -|- _valid_loc l.
  Proof.
    rewrite valid_loc_eq /valid_loc_def addr_of_eq /addr_of_def /_location /=.
    split'; first by iDestruct 1 as (?) "[_ $]".
    iIntros "V"; iExists (_loc_eval l). by iFrame.
  Qed.

  Global Instance valid_loc_proper : Proper ((≡) ==> (≡)) valid_loc.
  Proof. rewrite valid_loc_eq. solve_proper. Qed.
  Global Instance valid_loc_mono : Proper ((≡) ==> (⊢)) valid_loc.
  Proof. rewrite valid_loc_eq. solve_proper. Qed.
  Global Instance valid_loc_flip_mono : Proper ((≡) ==> flip (⊢)) valid_loc.
  Proof.
    rewrite valid_loc_eq /valid_loc_def=>l1 l2 HL/=. by setoid_rewrite HL.
  Qed.

  Global Instance valid_loc_persistent : Persistent (valid_loc l).
  Proof. rewrite valid_loc_eq. apply _. Qed.
  Global Instance valid_loc_affine : Affine (valid_loc l).
  Proof. rewrite valid_loc_eq. apply _. Qed.
  Global Instance valid_loc_timeless : Timeless (valid_loc l).
  Proof. rewrite valid_loc_eq. apply _. Qed.

  (** offsets *)

  Global Instance Offset_Equiv : Equiv Offset :=
    fun o1 o2 => _offset_eval o1 = _offset_eval o2 /\ (forall p, _valid_offset o1 p -|- _valid_offset o2 p).

  Global Instance Offset_Equivalence : Equivalence (≡@{Offset}).
  Proof.
    split.
    - done.
    - do 3 red. intros * [??]. by split; symmetry.
    - do 3 red. intros * [? E1] [? E2]. split. by etrans.
      move=> p. by rewrite E1 E2.
  Qed.

  Local Program Definition invalidO : Offset := MkOffset None (funI _ => False) _.
  Next Obligation. iIntros "% []". Qed.

  Program Definition offsetO (o : Z) : Offset :=
    MkOffset (Some o) (funI p => □ (valid_ptr p -* valid_ptr (offset_ptr_ o p))) _.
  Next Obligation. iIntros (??) "#$ /=". Qed.

  (* refine {| _offset from to := [| to = offset_ptr_ o from |] ** valid_ptr to |}.
  abstract (intros; iIntros "[[#H _] [-> _]]"; iFrame "#").
  abstract (intros; iIntros "[A [B C]]"; iFrame).
  Defined. *)

  Definition offsetO_opt (o : option Z) : Offset :=
    match o with
    | None => invalidO
    | Some o => offsetO o
    end.

  (** the identity [Offset] *)
  Definition _id_def : Offset := offsetO 0.
  Definition _id_aux : seal (@_id_def). Proof. by eexists. Qed.
  Definition _id := _id_aux.(unseal).
  Definition _id_eq : @_id = _ := _id_aux.(seal_eq).

  (** path composition *)
  Definition raw_compose_offsets (o1 o2 : raw_ptr_offset) : raw_ptr_offset :=
    z1 ← o1; z2 ← o2; Some (z1 + z2)%Z.
  Definition compose_offsets (o1 o2 : Offset) : raw_ptr_offset :=
    raw_compose_offsets (_offset_eval o1) (_offset_eval o2).
  Definition Offset_ptr o p := raw_offset_ptr_ (_offset_eval o) p.
  (* XXX lift up. *)
  Global Arguments compose_offsets _ _ /.
  Global Arguments Offset_ptr !_ /.

  (* We have a monoid action? Argh. *)
  Lemma raw_offset_ptr_compose_offsets o1 o2 p :
    raw_offset_ptr_ (compose_offsets o1 o2) p =
    Offset_ptr o2 (Offset_ptr o1 p).
  Proof.
    rewrite /Offset_ptr/=.
    case: (_offset_eval o1) => [z1| ] /=; first last.
    by rewrite raw_offset_invalid_ptr.
    case: (_offset_eval o2) => [z2| ] //=.
    by rewrite offset_ptr_combine_.
  Qed.

  Program Definition _dot_def (o1 o2 : Offset) : Offset :=
  MkOffset (compose_offsets o1 o2)
    (funI p => _valid_offset o1 p ** _valid_offset o2 (Offset_ptr o1 p)) _.
  Next Obligation.
    iIntros (???) "/= [O1 O2] P /=".
    rewrite raw_offset_ptr_compose_offsets.
    iApply (_offset_eval_valid with "O2").
    iApply (_offset_eval_valid with "O1 P").
  Qed.
  Definition _dot_aux : seal (@_dot_def). Proof. by eexists. Qed.
  Definition _dot := _dot_aux.(unseal).
  Definition _dot_eq : @_dot = _ := _dot_aux.(seal_eq).


  (** access a field *)
  Definition _field_def (resolve: genv) (f : field) : Offset :=
    offsetO_opt (offset_of resolve f.(f_type) f.(f_name)).
  Definition _field_aux : seal (@_field_def). Proof. by eexists. Qed.
  Definition _field := _field_aux.(unseal).
  Definition _field_eq : @_field = _ := _field_aux.(seal_eq).

  (** subscript an array *)
  Definition _sub_def (resolve:genv) (t : type) (i : Z) : Offset :=
    offsetO_opt (match size_of resolve t with
                 | Some o => Some (Z.of_N o * i)%Z
                 | _ => None
                 end).
  Definition _sub_aux : seal (@_sub_def). Proof. by eexists. Qed.
  Definition _sub := _sub_aux.(unseal).
  Definition _sub_eq : @_sub = _ := _sub_aux.(seal_eq).

  (** [_base derived base] is a cast from derived to base.
   *)
  Definition _base_def (resolve:genv) (derived base : globname) : Offset :=
    offsetO_opt (parent_offset resolve derived base).
  Definition _base_aux : seal (@_base_def). Proof. by eexists. Qed.
  Definition _base := _base_aux.(unseal).
  Definition _base_eq : @_base = _ := _base_aux.(seal_eq).
  Definition _super := _base.

  (** [_derived base derived] is a cast from base to derived
   *)
  Definition _derived_def (resolve:genv) (base derived : globname) : Offset :=
    offsetO_opt match parent_offset resolve derived base with
                | Some o => Some (0 - o)%Z
                | None => None
                end.
  Definition _derived_aux : seal (@_derived_def). Proof. by eexists. Qed.
  Definition _derived := _derived_aux.(unseal).
  Definition _derived_eq : @_derived = _ := _derived_aux.(seal_eq).

  (** offset from a location
   *)
  Program Definition _offsetL_def (o : Offset) (l : Loc) : Loc :=
    MkLoc (Offset_ptr o (_loc_eval l)) (_valid_loc l ** _valid_offset o (_loc_eval l)) _.
  Next Obligation.
    iIntros (??) "[P O]".
    iApply (_offset_eval_valid with "O").
    by iApply _loc_eval_valid.
  Qed.
  Definition _offsetL_aux : seal (@_offsetL_def). Proof. by eexists. Qed.
  Definition _offsetL := _offsetL_aux.(unseal).
  Definition _offsetL_eq : @_offsetL = _ := _offsetL_aux.(seal_eq).

  (* XXX NOTE: This lemma requires the equivalences to become more intensional. *)
  Global Instance _offsetL_proper : Proper ((≡) ==> (≡) ==> (≡)) _offsetL.
  Proof.
    move =>o1 o2 [Hoe Hove] l1 l2 [Hle Hlve].
    rewrite _offsetL_eq /_offsetL_def; split => /=.
    (* XXX Offset_ptr should be proper *)
    (* XXX missing LOTS of setoids *)
    by rewrite Hle /Offset_ptr Hoe.
    by rewrite Hlve Hle Hove.
  Qed.

  Global Arguments Offset_ptr !_ /. (* XXX *)
  Lemma _offsetL_dot (o1 o2 : Offset) (l : Loc) :
      _offsetL o2 (_offsetL o1 l) -|- _offsetL (_dot o1 o2) l.
  Proof.
    rewrite /equiv /Loc_Equiv _offsetL_eq _dot_eq /=.
    rewrite !raw_offset_ptr_compose_offsets /_dot_def /=.
    by rewrite assoc.
  Qed.
  Global Instance: Assoc eq raw_compose_offsets.
  Proof. move=> [x| ] [y| ] [z| ] //=. f_equiv. lia. Qed.

  Lemma _dot_dot (o1 o2 l: Offset) :
      _dot o2 (_dot o1 l) -|- _dot (_dot o2 o1) l.
  Proof.
    rewrite /equiv /Offset_Equiv _dot_eq/= -assoc.
    split => [//|p].
    by rewrite raw_offset_ptr_compose_offsets -assoc.
  Qed.

  (* Global Arguments _location !_ /. *)
  (* XXX Fix Loc_equiv to match Loc_Equiv. And without rewriting it properly! *)
  Lemma _offsetL_Loc_impl : forall l1 l2 o,
      Loc_equiv l1 l2 |-- Loc_equiv (_offsetL o l1) (_offsetL o l2).
  Proof.
    intros.
    rewrite /Loc_equiv _offsetL_eq /_offsetL_def /=.
    iIntros "[-> #A]". iSplit; first done. iIntros "!>".
    by iSplit; iIntros "[? $]"; iApply "A".
  Qed.

  (* this is for `Indirect` field references *)
  Fixpoint path_to_Offset (resolve:genv) (from : globname) (final : ident)
           (ls : list (ident * globname))
    : Offset :=
    match ls with
    | nil => @_field resolve {| f_type := from ; f_name := final |}
    | cons (i,c) ls =>
      _dot (@_field resolve {| f_type := from ; f_name := i |}) (path_to_Offset resolve c final ls)
    end.

  Definition offset_for (resolve:genv) (cls : globname) (f : FieldOrBase) : Offset :=
    match f with
    | Base parent => _super resolve cls parent
    | Field i => _field resolve {| f_type := cls ; f_name := i |}
    | Indirect ls final =>
      path_to_Offset resolve cls final ls
    | This => _id
    end.

End with_Σ.

Arguments addr_of : simpl never.
Notation "a &~ b" := (addr_of a b) (at level 30, no associativity).

Global Opaque _sub _field _offsetL _dot addr_of.

Arguments _super {_ Σ} {resolve} _ _ : rename.
Arguments _field {_ Σ} {resolve} _ : rename.
Arguments _sub {_ Σ} {resolve} _ : rename.
Arguments _global {_ Σ} {resolve} _ : rename.
