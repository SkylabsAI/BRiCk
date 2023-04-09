(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(**
Another (incomplete) consistency proof for [PTRS], based on Krebbers' PhD thesis, and
other formal models of C++ using structured pointers.
This is more complex than [SIMPLE_PTRS_IMPL], but will be necessary to justify [VALID_PTR_AXIOMS].

In this model, all valid pointers have an address pinned, but this is not meant
to be guaranteed.
*)

From Coq.Logic Require Import IndefiniteDescription PropExtensionality.
From stdpp Require Import gmap.
From bedrock.prelude Require Import base addr avl bytestring option numbers finite.
Require Import bedrock.prelude.elpi.derive.

From bedrock.lang.cpp Require Import ast.
From bedrock.lang.cpp.semantics Require Import sub_module values.
From bedrock.lang.cpp.model Require Import simple_pointers_utils inductive_pointers_utils.

Implicit Types (σ : genv) (z : Z).
#[local] Close Scope nat_scope.
#[local] Open Scope Z_scope.

Import canonical_tu address_sums merge_elems.

(* This is probably not generally applicable. *)
#[local] Arguments liftM2 {_ _ _ _ _ _} _ !_ !_ / : simpl nomatch.

Module Import PTRS_AUX.

  Inductive raw_offset_seg : Set :=
  | o_field_ (* type-name: *) (f : field)
  | o_sub_ (ty : type) (z : Z)
  | o_base_ (derived base : globname)
  | o_derived_ (base derived : globname)
  | o_invalid_.
  #[export] Instance raw_offset_seg_eq_dec : EqDecision raw_offset_seg.
  Proof. solve_decision. Defined.
  #[global] Declare Instance raw_offset_seg_countable : Countable raw_offset_seg.

  Definition offset_seg : Set := raw_offset_seg * Z.
  #[export] Instance offset_seg_eq_dec : EqDecision offset_seg := _.
  #[export] Instance offset_seg_countable : Countable offset_seg := _.

  Definition eval_raw_offset_seg σ (ro : raw_offset_seg) : option Z :=
    match ro with
    | o_field_ f => o_field_off σ f
    | o_sub_ ty z => o_sub_off σ ty z
    | o_base_ derived base => o_base_off σ derived base
    | o_derived_ base derived => o_derived_off σ base derived
    | o_invalid_ => None
    end.
  Definition mk_offset_seg σ (ro : raw_offset_seg) : offset_seg :=
    match eval_raw_offset_seg σ ro with
    | None => (o_invalid_, 0%Z)
    | Some off => (ro, off)
    end.
  #[global] Arguments mk_offset_seg _ !_ /.

  (* This list is reversed.
  The list of offsets in [[p; o_1; ...; o_n]] is represented as [[o_n; ... o_1]].
  This way, we can cons new offsets to the head, and consume them at the tail. *)
  Definition raw_offset := list offset_seg.
  #[export] Instance raw_offset_eq_dec : EqDecision raw_offset := _.
  #[export] Instance raw_offset_countable : Countable raw_offset := _.

  (* This is probably sound, since it allows temporary underflows. *)
  Definition eval_offset_seg (os : offset_seg) : option Z :=
    match os with
    | (o_invalid_, _) => None
    | (_, z) => Some z
    end.
  Definition eval_raw_offset (o : raw_offset) : option Z :=
    foldr (liftM2 Z.add) (Some 0) (map eval_offset_seg o).

  Notation isnt o pattern :=
    (match o with | pattern => False | _ => True end).

  Inductive root_ptr : Set :=
  | nullptr_
  | global_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | alloc_ptr_ (aid_base : N) (va : vaddr).

  #[export] Instance root_ptr_eq_dec : EqDecision root_ptr.
  Proof. solve_decision. Defined.
  #[global] Declare Instance root_ptr_countable : Countable root_ptr.
  #[global] Instance global_ptr__inj : Inj2 (=) (=) (=) global_ptr_.
  Proof. by intros ???? [=]. Qed.

  Definition root_ptr_vaddr (rp : root_ptr) : option vaddr :=
    match rp with
    | nullptr_ => Some 0%N
    | global_ptr_ tu o => Some (global_ptr_encode_vaddr o)
    | alloc_ptr_ aid va => Some va
    end.

End PTRS_AUX.

(* Classical quotients. Inspired by Lean 3's library. TODO license. *)
Parameter quotient : ∀ (A : Set) (R : relation A), Set.
Infix "/" := quotient.
Module cquot.
  Section cquot.
    Context {A : Set} {R : relation A}.

    Parameter mk : A -> A / R.
    Parameter lift : ∀ {B} (f : A -> B) (Heq : ∀ x y : A, R x y -> f x = f y), A / R -> B.
    Axiom ind : ∀ (P : A / R -> Prop),
      (∀ x : A, P (mk x)) -> (∀ q : A / R, P q).

    Axiom sound : ∀ x y : A, R x y -> mk x = mk y.

    Axiom lift_beta : ∀ {B} {f : A -> B} {Heq x},
      lift f Heq (mk x) = f x.

    #[program] Definition lift2 `{!Reflexive R} {B} (f : A -> A -> B)
        (Heq : ∀ a11 a12 a21 a22,
          R a11 a12 -> R a21 a22 -> f a11 a21 = f a12 a22)
        (q1 q2 : A / R) : B :=
      cquot.lift (λ ro1, cquot.lift (f ro1) _ q2) _ q1.
    Next Obligation. intros. exact: Heq. Qed.
    (* Next Obligation. intros. rewrite /= (choose_eq q2) !lift_beta. exact: Heq. Qed. *)
    Next Obligation. simpl. intros. induction q2 as [z] using ind. rewrite !lift_beta. exact: Heq. Qed.

    Lemma lift2_beta `{!Reflexive R} {B} (f : A -> A -> B) Heq a1 a2 :
      cquot.lift2 f Heq (mk a1) (mk a2) = f a1 a2.
    Proof. by rewrite /lift2 !lift_beta. Qed.

    (* Not very computational; don't care. *)
    #[global] Declare Instance quot_eq_dec : EqDecision A -> EqDecision (A / R).

    Lemma sound_surj_prop : ∀ q : A / R,
      ∃ a : A, q = mk a.
    Proof. by induction q as [x] using ind; exists x. Qed.

    Lemma sound_surj : ∀ q : A / R,
      { a : A | q = mk a }.
    Proof. intros. apply constructive_indefinite_description, sound_surj_prop. Qed.

    Definition choose (q : A / R) : A := proj1_sig (sound_surj q).
    Lemma choose_eq q :
      q = mk (choose q).
    Proof. rewrite /choose. by case: sound_surj. Qed.

    #[global, program] Instance quot_countable `{Countable A} : Countable (A / R) := {|
      encode x := encode (choose x);
      decode n := mk <$> decode n;
    |}.
    Next Obligation. by intros ?? x; rewrite /= decode_encode /= -choose_eq. Qed.

    #[program] Definition quot_rel `{!Equivalence R} : relation (A / R) :=
      λ x y, lift2 R _ x y.
    Next Obligation.
      intros ??? * H1 H2.
      apply propositional_extensionality.
      by rewrite H1 H2.
    Qed.
    Lemma rel_beta x y `{!Equivalence R} : quot_rel (mk x) (mk y) <-> R x y.
    Proof. by rewrite /quot_rel lift2_beta. Qed.

    Lemma rel_eq x y `{!Equivalence R} : quot_rel x y <-> x = y.
    Proof.
      induction x as [x] using ind; induction y as [y] using ind.
      split; last (intros <-); rewrite !rel_beta //.
      apply sound.
    Qed.

    #[global] Instance rel_equiv `{!Equivalence R} : Equivalence quot_rel.
    Proof.
      split; move; induction x as [x] using ind;
        try induction y as [y] using ind;
        try induction z as [z] using ind.
      all: rewrite !rel_beta //. by etrans.
    Qed.

    Lemma choose_sound a `{!Equivalence R} :
      R (choose (mk a)) a.
    Proof.
      rewrite /choose/=.
      case: sound_surj =>/= x H.
      by rewrite -rel_beta H.
    Qed.
    #[local] Instance : RewriteRelation R := {}.
  End cquot.
End cquot.

Module PTRS_IMPL <: PTRS_INTF.
  (* WIP: alternative, simpler model, using an equivalence relation and classical quotients. *)
  Module roff_equiv.
    Inductive roff_equiv : raw_offset -> raw_offset -> Prop :=
    | o_nil :
      roff_equiv [] []
    | o_cons r os1 os2 :
      roff_equiv os1 os2 ->
      roff_equiv (r :: os1) (r :: os2)
    | o_base_derived1 derived base o os1 os2 :
      roff_equiv os1 os2 ->
      roff_equiv ((o_base_ derived base, o) :: (o_derived_ base derived, -o) :: os1) os2
    | o_base_derived2 derived base o os1 os2 :
      roff_equiv os1 os2 ->
      roff_equiv os1 ((o_base_ derived base, o) :: (o_derived_ base derived, -o) :: os2)
    | o_derived_base1 derived base o os1 os2 :
      roff_equiv os1 os2 ->
      roff_equiv ((o_derived_ base derived, o) :: (o_base_ derived base, -o) :: os1) os2
    | o_derived_base2 derived base o os1 os2 :
      roff_equiv os1 os2 ->
      roff_equiv os1 ((o_derived_ base derived, o) :: (o_base_ derived base, -o) :: os2)
    | o_sub_0_equiv1 os1 os2 ty :
      roff_equiv os1 os2 ->
      roff_equiv ((o_sub_ ty 0, 0) :: os1) os2
    | o_sub_0_equiv2 os1 os2 ty :
      roff_equiv os1 os2 ->
      roff_equiv os1 ((o_sub_ ty 0, 0) :: os2)
    | o_sub_sub1 os1 os2 ty z1 z2 o1 o2 :
      roff_equiv os1 os2 ->
      roff_equiv ((o_sub_ ty z1, o1) :: (o_sub_ ty z2, o2) :: os1) ((o_sub_ ty (z1 + z2), o1 + o2) :: os2)
    | o_sub_sub2 os1 os2 ty z1 z2 o1 o2 :
      roff_equiv os1 os2 ->
      roff_equiv ((o_sub_ ty (z1 + z2), o1 + o2) :: os1) ((o_sub_ ty z1, o1) :: (o_sub_ ty z2, o2) :: os2)
    | o_invalid1 os z1 z2 :
      roff_equiv ((o_invalid_, z1) :: os) [(o_invalid_, z2)]
    | o_invalid2 os z1 z2 :
      roff_equiv [(o_invalid_, z1)] ((o_invalid_, z2) :: os)
    | o_trans os1 os2 os3 :
      roff_equiv os1 os2 ->
      roff_equiv os2 os3 ->
      roff_equiv os1 os3
    .

    #[local] Hint Constructors roff_equiv : core.
    #[local] Remove Hints o_trans : core.

    #[local] Instance: Reflexive roff_equiv.
    Proof. intros ro; induction ro; auto. Qed.
    #[local] Instance: Transitive roff_equiv.
    Proof. apply: o_trans. Qed.
    #[local] Instance: Symmetric roff_equiv.
    Proof. induction 1; try by constructor. by etrans. Qed.
    #[export] Instance: Equivalence roff_equiv.
    Proof. split; apply _. Qed.

    Definition eval_raw_offset (os : raw_offset) : option Z :=
      foldr (liftM2 Z.add) (Some 0) (eval_offset_seg <$> os).

      (* foldr (Z.add) 0%Z (snd <$> os). *)
    #[global] Arguments eval_raw_offset !_ /.
    Lemma eval_raw_offset_proper (x y : raw_offset) :
      roff_equiv x y → eval_raw_offset x = eval_raw_offset y.
    Proof.
      elim => > // _; try lia.
      all: rewrite /eval_raw_offset ?fmap_cons /= => -> //.
      all: case: (foldr _ _ _) => //= a; apply (f_equal Some); lia.
    Qed.

    Lemma roff_equiv_app a11 a12 a21 a22 :
      roff_equiv a11 a12 ->
      roff_equiv a21 a22 ->
      roff_equiv (a21 ++ a11) (a22 ++ a12).
    Proof.
      move=> + H. move: a11 a12.
      induction H => //=; eauto.
      3: { etrans; first eauto. exact: IHroff_equiv2. }
      intros. etrans. apply o_invalid1. apply (o_invalid2 _ 0).
      intros. etrans. apply o_invalid1. apply (o_invalid2 _ 0).
    Qed.
  End roff_equiv.
  Import roff_equiv.

  Definition offset := raw_offset / roff_equiv.
  #[global] Instance offset_eq_dec : EqDecision offset := _.
  #[global] Instance offset_countable : Countable offset := _.

  Definition eval_offset' : offset -> option Z :=
    cquot.lift eval_raw_offset eval_raw_offset_proper.
  Lemma eval_offset'_eq ro :
    eval_offset' (cquot.mk ro) = eval_raw_offset ro.
  Proof. apply cquot.lift_beta. Qed.

  Definition o_id : offset := cquot.mk [].
  Program Definition mkOffset σ (ro : raw_offset_seg) : offset :=
    cquot.mk [mk_offset_seg σ ro].
  Definition o_invalid σ : offset := mkOffset σ o_invalid_.
  Definition o_field σ f : offset :=
    mkOffset σ (o_field_ f).
  Definition o_base σ derived base : offset :=
    mkOffset σ (o_base_ derived base).
  Definition o_derived σ base derived : offset :=
    mkOffset σ (o_derived_ base derived).
  Program Definition o_sub σ ty z : offset :=
    mkOffset σ (o_sub_ ty z).

  Inductive base_ptr : Set :=
  | invalid_ptr_
  | fun_ptr_ (tu : translation_unit_canon) (o : obj_name)
  | root (p : root_ptr).
  #[global] Instance base_ptr_eq_dec : EqDecision base_ptr.
  Proof. solve_decision. Defined.
  #[global] Instance root_inj : Inj (=) (=) root.
  Proof. by intros ?? [=]. Qed.

  Definition ptr : Set := base_ptr * offset.
  Definition offset_ptr : base_ptr -> offset -> ptr := pair.
  #[global] Instance ptr_eq_dec : EqDecision ptr.
  Proof. solve_decision. Defined.
  #[local] Instance ptr_eq_dec' : EqDecision ptr := ptr_eq_dec.
  #[global] Declare Instance ptr_countable : Countable ptr.
  #[global] Instance offset_ptr_inj : Inj2 (=) (=) (=) offset_ptr.
  Proof. by intros ???? [=]. Qed.

  Variant alloc_id_aux :=
  | null_alloc_id_
  | global_id_ (va : vaddr)
  | alloc_id_ (id : N).
  #[global] Instance global_id__inj : Inj (=) (=) global_id_.
  Proof. by intros ??[=]. Qed.
  #[only(eq_dec)] derive alloc_id_aux.
  #[global] Instance : Countable alloc_id_aux.
  Proof.
    set (g := λ a : alloc_id_aux,
      match a with
      | null_alloc_id_ => inl (inl tt)
      | global_id_ va => inl (inr va)
      | alloc_id_ aid => inr aid
      end).
    set (f := λ s : unit + N + N,
      match s with
      | inl (inl tt) => null_alloc_id_
      | inl (inr va) => global_id_ va
      | inr aid => alloc_id_ aid
      end).
    apply (inj_countable' (A := unit + N + N) g f).
    abstract (by case).
  Defined.

  Definition root_ptr_alloc_id_aux (rp : root_ptr) : alloc_id_aux :=
      match rp with
      | nullptr_ => null_alloc_id_
      | global_ptr_ tu o => global_id_ (global_ptr_encode_vaddr o)
      | alloc_ptr_ aid _ => alloc_id_ aid
      end.
  (* The above definition ensures alloc_ids are disjoint between different
  classes.
  XXX: we ignore TUs? They don't really help anyway, we should store the genv in there...
  *)
  (* Shadowing: *)

  Definition ptr_alloc_id_aux (p : ptr) : option alloc_id_aux :=
    match fst p with
    | invalid_ptr_ => None
    | fun_ptr_ tu o => Some (global_id_ (global_ptr_encode_vaddr o))
    | root p => Some (root_ptr_alloc_id_aux p)
    end.
  Definition alloc_id_aux2alloc_id (a : alloc_id_aux) : alloc_id :=
    MkAllocId (encode_N a).
  #[global] Instance alloc_id_aux2alloc_id_inj : Inj (=) (=) alloc_id_aux2alloc_id := _.

  Definition ptr_alloc_id (p : ptr) : option alloc_id :=
    alloc_id_aux2alloc_id <$> ptr_alloc_id_aux p.

  Definition base_ptr_vaddr (p : base_ptr) : option vaddr :=
    match p with
    | invalid_ptr_ => None
    | fun_ptr_ tu o => Some (global_ptr_encode_vaddr o)
    | root p =>
      root_ptr_vaddr p
    end.

  Definition ptr_vaddr (p : ptr) : option vaddr :=
    va ← base_ptr_vaddr (fst p);
    off ← eval_offset' (snd p);
    offset_vaddr off va.
  #[global] Arguments ptr_vaddr !_ /.

  Definition lift_root_ptr (rp : root_ptr) : ptr := (root rp, o_id).
  #[global] Instance lift_root_ptr_inj : Inj (=) (=) lift_root_ptr.
  Proof. by intros ?? [=]. Qed.
  Lemma ptr_vaddr_root_ptr rp :
    ptr_vaddr (lift_root_ptr rp) = root_ptr_vaddr rp.
  Proof.
    rewrite /lift_root_ptr/= eval_offset'_eq.
    case: root_ptr_vaddr => //= va.
    by rewrite offset_vaddr_0.
  Qed.

  Definition invalid_ptr : ptr := (invalid_ptr_, o_id).
  Definition fun_ptr tu o : ptr := (fun_ptr_ (canonical_tu.tu_to_canon tu) o, o_id).

  Definition nullptr : ptr := lift_root_ptr nullptr_.
  Definition global_ptr (tu : translation_unit) o :=
    lift_root_ptr (global_ptr_ (canonical_tu.tu_to_canon tu) o).
  Definition alloc_ptr a oid := lift_root_ptr (alloc_ptr_ a oid).

  Lemma global_ptr_nonnull tu o : global_ptr tu o <> nullptr.
  Proof. done. Qed.

  #[global] Instance global_ptr_inj tu : Inj (=) (=) (global_ptr tu).
  Proof.
    rewrite /global_ptr.
    by intros ?? []%(inj lift_root_ptr)%(inj2 global_ptr_).
  Qed.

  (* Some proofs using these helpers could be shortened, tactic-wise, but I find
  them clearer this way, and they work in both models. *)
  Lemma ptr_vaddr_global_ptr tu o :
    ptr_vaddr (global_ptr tu o) = Some (global_ptr_encode_vaddr o).
  Proof. apply ptr_vaddr_root_ptr. Qed.

  Definition null_alloc_id : alloc_id := alloc_id_aux2alloc_id null_alloc_id_.
  Lemma ptr_alloc_id_nullptr : ptr_alloc_id nullptr = Some null_alloc_id.
  Proof. done. Qed.
  Definition global_ptr_encode_aid o :=
    alloc_id_aux2alloc_id (global_id_ (global_ptr_encode_vaddr o)).
  #[global] Instance global_ptr_encode_aid_inj : Inj (=) (=) global_ptr_encode_aid := _.

  Lemma ptr_alloc_id_global_ptr tu o :
    ptr_alloc_id (global_ptr tu o) = Some (global_ptr_encode_aid o).
  Proof. done. Qed.

  Lemma global_ptr_nonnull_addr tu o : ptr_vaddr (global_ptr tu o) <> Some 0%N.
  Proof. rewrite ptr_vaddr_global_ptr. done. Qed.
  Lemma global_ptr_nonnull_aid tu o : ptr_alloc_id (global_ptr tu o) <> Some null_alloc_id.
  Proof.
    rewrite ptr_alloc_id_global_ptr /null_alloc_id /global_ptr_encode_aid.
    by intros ?%(inj _)%(inj _).
  Qed.

  #[global] Instance global_ptr_addr_inj tu : Inj (=) (=) (λ o, ptr_vaddr (global_ptr tu o)).
  Proof. intros ??. rewrite !ptr_vaddr_global_ptr. by intros ?%(inj _)%(inj _). Qed.
  #[global] Instance global_ptr_aid_inj tu : Inj (=) (=) (λ o, ptr_alloc_id (global_ptr tu o)).
  Proof. intros ??. rewrite !ptr_alloc_id_global_ptr. by intros ?%(inj _)%(inj _). Qed.

  Lemma ptr_vaddr_nullptr : ptr_vaddr nullptr = Some 0%N.
  Proof. apply ptr_vaddr_root_ptr. Qed.


  #[program] Definition __o_dot (o1 o2 : offset) : offset :=
    cquot.lift2 (λ ro1 ro2, cquot.mk (ro2 ++ ro1)) _ o1 o2.
  Next Obligation. intros; exact /cquot.sound /roff_equiv_app. Qed.
  Lemma __o_dot_eq (ro1 ro2 : raw_offset) :
    __o_dot (cquot.mk ro1) (cquot.mk ro2) = cquot.mk (ro2 ++ ro1).
  Proof. by rewrite /__o_dot cquot.lift2_beta /=. Qed.

  Definition __offset_ptr (p : ptr) (o : offset) : ptr :=
    (fst p, __o_dot (snd p) o).

  Include PTRS_SYNTAX_MIXIN.
  (* Duplicated. *)
  #[global] Notation "p ., o" := (_dot p (o_field _ o))
    (at level 11, left associativity, only parsing) : stdpp_scope.

  #[local] Ltac UNFOLD_dot := rewrite _dot.unlock/DOT_dot/=.
  Definition eval_offset σ o := eval_offset' o.
  Lemma eval_offset_eq σ ro :
    eval_offset σ (cquot.mk ro) = eval_raw_offset ro.
  Proof. apply eval_offset'_eq. Qed.

  Lemma foldr_unit {A} (f : A -> A -> A) (z : A) (xs ys : list A) `{!LeftId (=) z f} `{!Assoc (=) f}:
    fold_right f z (xs ++ ys) =
    f (fold_right f z xs) (fold_right f z ys).
  Proof.
    elim: xs => [//|x xs IH]; cbn. by rewrite {}IH assoc_L.
  Qed.

  #[global] Instance : Comm (=) add_opt.
  Proof. move=> [b1|] [b2|] //=. by rewrite comm_L. Qed.
  #[global] Instance : LeftId (=) (Some 0) add_opt.
  Proof. by move=> [b1|]. Qed.
  #[global] Instance : Assoc (=) add_opt.
  Proof. move=> [b1|] [b2|] [b3|] //=. by rewrite assoc_L. Qed.

  Lemma eval_raw_offset_app ro1 ro2 :
    eval_raw_offset (ro2 ++ ro1) =
    add_opt (eval_raw_offset ro1) (eval_raw_offset ro2).
  Proof. by rewrite (comm_L add_opt) /eval_raw_offset fmap_app foldr_unit. Qed.

  (* [eval_offset] respects the monoidal structure of [offset]s *)
  Lemma eval_offset_dot σ (o1 o2 : offset) :
    eval_offset σ (o1 ,, o2) =
    add_opt (eval_offset σ o1) (eval_offset σ o2).
  Proof.
    intros **; UNFOLD_dot.
    induction o1 as [ro1] using cquot.ind.
    induction o2 as [ro2] using cquot.ind.
    by rewrite __o_dot_eq !eval_offset_eq eval_raw_offset_app.
  Qed.

  #[global] Instance id_dot : LeftId (=) o_id o_dot.
  Proof.
    intros o; UNFOLD_dot.
    induction o as [ro] using cquot.ind.
    by rewrite __o_dot_eq app_nil_r.
  Qed.

  Lemma __o_dot_id : RightId (=) o_id __o_dot.
  Proof.
    intros o.
    induction o as [ro] using cquot.ind.
    by rewrite __o_dot_eq.
  Qed.
  #[global] Instance dot_id : RightId (=) o_id o_dot.
  Proof. UNFOLD_dot. apply __o_dot_id. Qed.
  #[global] Instance __dot_assoc : Assoc (=) __o_dot.
  Proof.
    intros o1 o2 o3.
    induction o1 as [ro1] using cquot.ind.
    induction o2 as [ro2] using cquot.ind.
    induction o3 as [ro3] using cquot.ind.
    by rewrite !__o_dot_eq assoc_L.
  Qed.

  #[global] Instance dot_assoc : Assoc (=) o_dot.
  Proof. UNFOLD_dot. apply _. Qed.

  Implicit Types (p : ptr) (o : offset).

  Lemma offset_ptr_id p : p ,, o_id = p.
  Proof. UNFOLD_dot. case: p => // p o. by rewrite /__offset_ptr __o_dot_id. Qed.

  Lemma offset_ptr_dot p o1 o2 : p ,, (o1 ,, o2) = p ,, o1 ,, o2.
  Proof. UNFOLD_dot. by rewrite /__offset_ptr/= assoc_L. Qed.

  Lemma o_sub_0 σ ty :
    is_Some (size_of σ ty) ->
    o_sub σ ty 0 = o_id.
  Proof.
    intros [n H].
    apply cquot.sound.
    rewrite /o_sub /= /o_sub_off/= H /=.
    exact: roff_equiv.o_sub_0_equiv1.
  Qed.

  Lemma ptr_alloc_id_offset {p o} :
    let p' := p ,, o in
    is_Some (ptr_alloc_id p') -> ptr_alloc_id p' = ptr_alloc_id p.
  Proof. by UNFOLD_dot. Qed.

  Lemma ptr_vaddr_o_sub_eq p σ ty n1 n2 sz :
    size_of σ ty = Some sz -> (sz > 0)%N ->
    same_property ptr_vaddr (p ,, o_sub _ ty n1) (p ,, o_sub _ ty n2) ->
    n1 = n2.
  Proof.
    rewrite same_property_iff.
    move=> Hsz Hpos [va []]; case: p => [b o].
    induction o as [os] using cquot.ind.
    UNFOLD_dot; case: base_ptr_vaddr => //= va'.
    rewrite !__o_dot_eq /= /o_sub_off Hsz/= !eval_offset'_eq; cbn.
    destruct (foldr _ _ _) as [Z|] => //=.
    intros HA%offset_vaddr_inv HB%offset_vaddr_inv; nia.
  Qed.

  #[local] Instance: RewriteRelation roff_equiv := {}.

  Lemma o_dot_sub σ (z1 z2 : Z) ty :
    o_sub σ ty z1 ,, o_sub σ ty z2 = o_sub σ ty (z1 + z2).
  Proof.
    rewrite comm_L.
    UNFOLD_dot; rewrite !__o_dot_eq.
    apply cquot.sound.
    rewrite /mk_offset_seg/= /o_sub_off/= /=.
    destruct size_of => //=; last apply o_invalid1.
    rewrite roff_equiv.o_sub_sub1; last reflexivity.
    repeat f_equiv; lia.
  Qed.

  Lemma _base_derived σ base derived :
    directly_derives σ derived base ->
    o_base σ derived base ,, o_derived σ base derived = o_id.
  Proof.
    intros [? Hsome].
    UNFOLD_dot; rewrite !__o_dot_eq /= /o_derived_off /o_base_off Hsome /=.
    rewrite -{2} (Z.opp_involutive x).
    exact /cquot.sound /o_derived_base1.
  Qed.

  Lemma _derived_base σ base derived :
    directly_derives σ derived base ->
    o_derived σ base derived ,, o_base σ derived base = o_id.
  Proof.
    intros [? Hsome].
    UNFOLD_dot; rewrite !__o_dot_eq /= /o_derived_off /o_base_off Hsome /=.
    exact /cquot.sound /o_base_derived1.
  Qed.

  Lemma o_base_derived σ p base derived :
    directly_derives σ derived base ->
    p ,, o_base σ derived base ,, o_derived σ base derived = p.
  Proof. intros. by rewrite -offset_ptr_dot _base_derived ?offset_ptr_id. Qed.

  Lemma o_derived_base σ p base derived :
    directly_derives σ derived base ->
    p ,, o_derived σ base derived ,, o_base σ derived base = p.
  Proof. intros. by rewrite -offset_ptr_dot _derived_base ?offset_ptr_id. Qed.

  Lemma eval_o_sub σ ty (i : Z) :
    eval_offset _ (o_sub _ ty i) =
      (* This order enables reducing for known ty. *)
      (fun n => Z.of_N n * i) <$> size_of _ ty.
  Proof.
    rewrite eval_offset_eq/=/o_sub_off/=.
    case: size_of=> [sz|] //=.
    by f_equal; lia.
  Qed.

  Lemma eval_o_field σ f n cls st :
    f = {| f_name := n ; f_type := cls |} ->
    glob_def σ cls = Some (Gstruct st) ->
    st.(s_layout) = POD \/ st.(s_layout) = Standard ->
    eval_offset σ (o_field σ f) = offset_of σ (f_type f) (f_name f).
  Proof.
    move => -> _ _. cbn.
    rewrite eval_offset_eq/=/o_field_off/=.
    case: offset_of => [off|//] /=. by rewrite right_id_L.
  Qed.

  Include PTRS_DERIVED_MIXIN.
  Include PTRS_MIXIN.
End PTRS_IMPL.
