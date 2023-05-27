(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.bi.ChargeCompat.
Require Import bedrock.lang.bi.telescopes.
Require Import bedrock.lang.cpp.logic.entailsN.
Require Import bedrock.lang.bi.errors.
Require Import iris.proofmode.proofmode.	(** Early to get the right [ident] *)
Require Import bedrock.lang.cpp.logic.
Require Import bedrock.lang.cpp.specs.cpp_specs.

#[local] Set Printing Universes.
#[local] Set Printing Coercions.

(** * Wrappers to build [function_spec] from a [WithPrePost] *)

Notation WithPrePostO PROP := (WpSpecO PROP ptr ptr).

#[local] Notation SPEC := (WpSpec_cpp_ptr) (only parsing).

(* A specification for a function *)
Definition SFunction `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (ret : type) (targs : list type) (PQ : SPEC)
    : function_spec :=
  {| fs_cc        := cc
   ; fs_this      := None
   ; fs_arity     := ar
   ; fs_return    := ret
   ; fs_arguments := targs
   ; fs_spec      := wp_specD PQ |}.

(* A specification for a member function.
   In the logic, we pass the [this] parameter as the first argument to the arguments of [fspec].
   [fspec (Tmember_func_ptr ..) ..] takes the [this] pointer as the first value.
   Note, we re-use this for constructors and destructors which act like like member functions.

   We generalize this slightly to support casting the [this] pointer within the function.
   For example, a virtual call to [Base::foo()] might call [Derived::foo()], so we want a way to
   lift the specification of [Dervied::foo()] to [Base::foo()] taking the downcast into account.
   It is not sufficient to do this on the denotation because we want to be able to change the
   argument that is passed, but not the ownership.
 *)
#[local] Definition member_to_function_spec `{Σ : cpp_logic}
    (base_to_derived : option offset) (wpp : ptr -> SPEC)
  : SPEC :=
  \arg{this : ptr} "this"
   (if base_to_derived is Some o then (this ,, o ) else this)
  \exact (wpp this).

#[local] Definition SMember_cast `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (class : globname) (base_to_derived : option offset) (qual : type_qualifiers) (rq : ref_qualifier.t)
    (ret : type) (targs : list type) (PQ : ptr -> SPEC) : function_spec :=
  let class_type := Tnamed class in
  let this_type := Tqualified qual class_type in
  {| fs_cc := cc
   ; fs_this := Some (class, ref_qualifier.None, QM)
   ; fs_arity := ar
   ; fs_return := Qmut Tvoid
   ; fs_arguments := targs
   ; fs_spec := member_to_function_spec base_to_derived PQ
   |}.
Definition SMethodCast `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (class : globname) (base_to_derived : offset) (qual : type_qualifiers) (rq : ref_qualifier.t)
    (ret : type) (targs : list type) (PQ : ptr -> SPEC) : function_spec :=
  SMember_cast (cc:=cc) class (Some base_to_derived) qual rq ret targs (ar:=ar) PQ.
Definition SMethod `{Σ : cpp_logic} {cc : calling_conv} {ar : function_arity}
    (class : globname) (qual : type_qualifiers) (rq : ref_qualifier.t) (ret : type) (targs : list type)
    (PQ : ptr -> SPEC) : function_spec :=
  SMember_cast (cc:=cc) class None qual rq ret targs (ar:=ar) PQ.

(* A specification for a constructor *)
Definition SConstructor `{Σ : cpp_logic, resolve : genv} {cc : calling_conv} {ar : function_arity}
    (class : globname) (targs : list type) (PQ : ptr -> SPEC)
    : function_spec :=
  SMember_cast (cc:=cc) (ar:=ar) class None QM ref_qualifier.None (Qmut Tvoid) targs
       (fun this : ptr =>
          \pre this |-> tblockR (Tnamed class) (cQp.mut 1)
          \exact PQ this).

(* A specification for a destructor *)
Definition SDestructor `{Σ : cpp_logic, resolve : genv} {cc : calling_conv}
    (class : globname) (PQ : ptr -> SPEC)
    : function_spec :=
  SMember_cast (cc:=cc) (ar:=Ar_Definite) class None QM ref_qualifier.None (Qmut Tvoid) nil
      (fun this : ptr =>
         add_post (this |-> tblockR (Tnamed class) (cQp.mut 1)) (PQ this)).

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  #[local] Notation _base := (o_base resolve).
  #[local] Notation _derived := (o_derived resolve).

  (** The following monotonicity lemmas are (i) stated so that they
      don't force a pair of related SPECs to share universes and (ii)
      proved so that they don't constrain the universes [Y1], [Y2]
      from above. The TC instances are strictly less useful, as they
      necessarily give up on both (i) and (ii). *)
  Section SFunction.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} {ar : function_arity}.
    Context (ret : type) (targs : list type).

    Lemma SFunction_mono wpp1 wpp2 :
      wpspec_entails wpp1 wpp2 ->
      fs_entails
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp1)
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp". by iApply Hwpp.
    Qed.

    Lemma SFunction_mono_fupd wpp1 wpp2 :
      wpspec_entails_fupd wpp1 wpp2 ->
      fs_entails_fupd
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp1)
        (SFunction (cc:=cc) (ar:=ar) ret targs wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SFunction_mono] *)
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp". by iApply Hwpp.
    Qed.

    #[global] Instance: Params (@SFunction) 6 := {}.
    #[global] Instance SFunction_ne : NonExpansive (SFunction (cc:=cc) ret targs).
    Proof.
      intros n wpp1 wpp2 Hwpp. split; by rewrite/type_of_spec/=.
    Qed.

    #[global] Instance SFunction_proper :
      Proper (equiv ==> equiv) (SFunction (cc:=cc) ret targs).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SFunction_mono' :
      Proper (wpspec_entails ==> fs_entails) (SFunction (cc:=cc) ret targs).
    Proof. repeat intro. by apply SFunction_mono. Qed.

    #[global] Instance SFunction_flip_mono' :
      Proper (flip wpspec_entails ==> flip fs_entails)
        (SFunction (cc:=cc) ret targs).
    Proof. solve_proper. Qed.

    #[global] Instance SFunction_mono_fupd' :
      Proper (wpspec_entails_fupd ==> fs_entails_fupd)
        (SFunction (cc:=cc) ret targs).
    Proof. repeat intro. by apply SFunction_mono_fupd. Qed.

    #[global] Instance SFunction_flip_mono_fupd' :
      Proper (flip wpspec_entails_fupd ==> flip fs_entails_fupd)
        (SFunction (cc:=cc) ret targs).
    Proof. solve_proper. Qed.
  End SFunction.

  Section SMember.
    Import disable_proofmode_telescopes.
    Context (cls : globname) (tq : type_qualifiers) (rq : ref_qualifier.t) (off : option offset).
    Context {cc : calling_conv} {ar : function_arity}.
    Context (ret : type) (targs : list type).
    #[local] Notation mspec_entails wpp1 wpp2 := (forall this : ptr, wpspec_entails (wpp1 this) (wpp2 this)) (only parsing).

    Lemma SMember_cast_mono wpp1 wpp2 :
      mspec_entails wpp1 wpp2 ->
      fs_entails
        (SMember_cast cls off tq rq (cc:=cc) (ar:=ar) ret targs wpp1)
        (SMember_cast cls off tq rq (cc:=cc) (ar:=ar) ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp".
      iStopProof. apply bi.exist_mono; intros.
      rewrite 2!spec_internal_denote.
      f_equiv. f_equiv; intro. f_equiv. apply Hwpp.
    Qed.

    Lemma SMember_cast_mono_fupd wpp1 wpp2 :
      (forall this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SMember_cast cls off tq rq (cc:=cc) (ar:=ar) ret targs wpp1)
        (SMember_cast cls off tq rq (cc:=cc) (ar:=ar) ret targs wpp2).
    Proof.
      intros Hwpp. iSplit; first by rewrite/type_of_spec. simpl.
      iIntros "!>" (vs K) "wpp".
      iDestruct "wpp" as (this) "wpp".
      rewrite spec_internal_denote.
      iDestruct "wpp" as "[? X]"; iDestruct "X" as (?) "[? B]".
      iDestruct (Hwpp with "B") as ">B". iModIntro.
      iExists this. rewrite spec_internal_denote.
      unfold wpspec_relation_fupd in Hwpp.
      iFrame. iExists _; iFrame.
      iRevert "B"; iApply spec_internal_frame.
      iIntros (?) "X Y". iMod "X". iModIntro. iApply "X". done.
    Qed.

    #[global] Instance: Params (@SMember_cast) 8 := {}.

    #[global] Instance SMember_cast_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SMember_cast cls off tq rq (cc:=cc) ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMember_cast_mono. Qed.

    #[global] Instance SMember_cast_flip_mono' :
      Proper (flip (pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SMember_cast cls off tq rq (cc:=cc) ret targs (ar:=ar)).
    Proof. solve_proper. Qed.

    #[global] Instance SMember_cast_mono_fupd' :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SMember_cast cls off tq rq (cc:=cc) ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMember_cast_mono_fupd. Qed.

    #[global] Instance SMember_cast_flip_mono_fupd' :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SMember_cast cls off tq rq (cc:=cc) ret targs (ar:=ar)).
    Proof. solve_proper. Qed.

    #[global] Instance SMember_cast_ne n :
      Proper (pointwise_relation _ (dist n) ==> dist n)
        (SMember_cast cls off tq rq (cc:=cc) ret targs (ar:=ar)).
    Proof.
      intros ???. rewrite /SMember_cast. constructor => //. simpl.
      constructor; intros. f_equiv. repeat f_equiv.
      rewrite !spec_internal_denote.
      repeat f_equiv. apply H.
    Qed.
    #[global] Instance SMember_cast_proper :
      Proper (pointwise_relation _ equiv ==> equiv)
        (SMember_cast cls off tq rq (cc:=cc) ret targs (ar:=ar)).
    Proof.
      intros ???. rewrite /SMember_cast. constructor => //. simpl.
      constructor; intros. f_equiv. repeat f_equiv.
      rewrite !spec_internal_denote.
      repeat f_equiv. apply H.
    Qed.

  End SMember.


  Section SConstructor.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} {ar : function_arity}.
    Context (class : globname) (targs : list type).
    Implicit Types (wpp : ptr → WpSpec mpredI ptr ptr).

    Lemma SConstructor_mono wpp1 wpp2 :
      (forall this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp1)
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp2).
    Proof.
      intros.
      eapply SMember_cast_mono.
      intros.
      rewrite /wpspec_entails/wp_specD/=.
      rewrite /fs_entails/fs_impl/SConstructor/fs_spec; intros.
      rewrite !spec_internal_denote.
      repeat f_equiv. apply H.
    Qed.
    #[global] Instance: Params (@SConstructor) 7 := {}.

    Lemma SConstructor_mono_fupd wpp1 wpp2 :
      (forall this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp1)
        (SConstructor (cc:=cc) class targs (ar:=ar) wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SConstructor_mono] *)
      rewrite /wpspec_entails_fupd/wp_specD/=.
      intros Hwpp; apply SMember_cast_mono_fupd => /=. intro.
      rewrite /wpspec_relation_fupd.
      iIntros (vs K) "wpp /=".
      rewrite !pre_ok.
      iDestruct "wpp" as "[$ wpp]".
      iDestruct (Hwpp with "wpp") as ">wpp". done.
    Qed.

    #[global] Instance SConstructor_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. repeat intro. by apply SConstructor_mono. Qed.

    #[global] Instance SConstructor_flip_mono' :
      Proper (flip (pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. solve_proper. Qed.

    #[global] Instance SConstructor_mono_fupd' :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. repeat intro. by apply SConstructor_mono_fupd. Qed.

    #[global] Instance SConstructor_flip_mono_fupd' :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. solve_proper. Qed.

    #[global] Instance SConstructor_ne n :
      Proper (pointwise_relation _ (dist n) ==> dist n)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. intros ???. apply SMember_cast_ne. repeat f_equiv. Qed.
    #[global] Instance SConstructor_proper :
      Proper (pointwise_relation _ equiv ==> equiv)
        (SConstructor (cc:=cc) class targs (ar:=ar)).
    Proof. intros ???. apply SMember_cast_proper. repeat f_equiv. Qed.
  End SConstructor.

  Section SDestructor.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} (class : globname).
    Implicit Types (wpp : ptr → WpSpec mpredI ptr ptr).

    Lemma SDestructor_mono wpp1 wpp2 :
      (forall this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SDestructor (cc:=cc) class wpp1)
        (SDestructor (cc:=cc) class wpp2).
    Proof.
      rewrite /wpspec_entails/wp_specD/=/SDestructor.
      intros Hwpp; apply SMember_cast_mono; intro.
      iIntros (vs K) "wpp /=".
      rewrite !spec_internal_denote.
      iStopProof; repeat f_equiv.
      rewrite Hwpp. f_equiv.
    Qed.
    #[global] Instance: Params (@SDestructor) 5 := {}.

    Lemma SDestructor_mono_fupd wpp1 wpp2 :
      (forall this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SDestructor (cc:=cc) class wpp1)
        (SDestructor (cc:=cc) class wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SDestructor_mono] *)
      rewrite /wpspec_entails_fupd/wp_specD/=/SDestructor.
      intros Hwpp; apply SMember_cast_mono_fupd; intros.
      iIntros (vs K) "wpp /=".
      rewrite !spec_internal_denote.
      iDestruct "wpp" as "[$ wpp]".
      iDestruct "wpp" as (?) "[X wpp]".
      rewrite Hwpp.
      iMod "wpp". iModIntro.
      iExists _; iFrame.
      iStopProof. iApply spec_internal_frame.
      iIntros (?) ">X Y". iModIntro; iApply "X"; done.
    Qed.

    #[global] Instance SDestructor_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SDestructor (cc:=cc) class).
    Proof. repeat intro. by apply SDestructor_mono. Qed.

    #[global] Instance SDestructor_flip_mono' :
      Proper (flip(pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SDestructor (cc:=cc) class).
    Proof. solve_proper. Qed.

    #[global] Instance SDestructor_mono_fupd' :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SDestructor (cc:=cc) class).
    Proof. repeat intro. by apply SDestructor_mono_fupd. Qed.

    #[global] Instance SDestructor_flip_mono_fupd' :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SDestructor (cc:=cc) class).
    Proof. solve_proper. Qed.

    #[global] Instance SDestructor_ne n :
      Proper (pointwise_relation _ (dist n) ==> dist n)
        (SDestructor (cc:=cc) class).
    Proof. intros ???. apply SMember_cast_ne. repeat f_equiv. Qed.
    #[global] Instance SDestructor_proper :
      Proper (pointwise_relation _ equiv ==> equiv)
        (SDestructor (cc:=cc) class).
    Proof. intros ???. apply SMember_cast_proper. repeat f_equiv. Qed.
  End SDestructor.

  Section SMethod.
    Import disable_proofmode_telescopes.
    Context {cc : calling_conv} {ar : function_arity}.
    Context (class : globname) (qual : type_qualifiers) (rq : ref_qualifier.t).
    Context (ret : type) (targs : list type).

    (** We could derive [SMethod_mono] from the following
        [SMethod_wpspec_monoN]. We retain this proof because it's easier
        to understand and it goes through without [BiEntailsN]. *)
    #[local] Lemma SMethodOptCast_mono cast wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp1)
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp2).
    Proof.
      intros Hwpp.
      apply SMember_cast_mono => this vs K.
      apply Hwpp.
    Qed.

    #[local] Lemma SMethodOptCast_None_Some_mono (off2 : offset) wpp1 wpp2 :
      (* NOTE (JH): contravariant use of casts *)
      (forall (thisp : ptr), wpspec_entails (wpp1 (thisp ,, off2)) (wpp2 thisp)) ->
      fs_entails
        (SMember_cast class None qual rq ret targs wpp1)
        (SMember_cast class (Some off2) qual rq ret targs wpp2).
    Proof.
      intros Hwpp.
      rewrite /SMember_cast.
      iSplit => /=//. iModIntro. iIntros (??) "X".
      iDestruct "X" as (this) "X".
      iExists (this ,, off2).
      rewrite !spec_internal_denote.
      iDestruct "X" as "[$ X]".
      iDestruct "X" as (aa) "[% X]".
      iExists aa.
      iFrame "%".
      iApply Hwpp. iApply "X".
    Qed.

    #[local] Lemma SMethodOptCast_mono_fupd cast wpp1 wpp2 :
      (∀ this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SMember_cast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp1)
        (SMember_cast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp2).
    Proof.
      (* (FM-2648) TODO duplicated from [SMethodOptCast_mono] *)
      intros Hwpp.
      apply SMember_cast_mono_fupd => this vs K.
      rewrite /= /exact_spec.
      iApply Hwpp.
    Qed.

    Lemma SMethodCast_mono cast wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SMember_cast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp1)
        (SMember_cast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp2).
    Proof. intro. apply: SMember_cast_mono; eauto. Qed.

    Lemma SMethodCast_None_Some_mono (off2 : offset) wpp1 wpp2 :
      (* NOTE (JH): contravariant use of casts *)
      (forall (thisp : ptr), wpspec_entails (wpp1 (thisp ,, off2)) (wpp2 thisp)) ->
      fs_entails
        (SMember_cast class None qual rq ret targs wpp1)
        (SMember_cast class (Some off2) qual rq ret targs wpp2).
    Proof. exact: SMethodOptCast_None_Some_mono. Qed.

    Lemma SMethod_mono wpp1 wpp2 :
      (∀ this, wpspec_entails (wpp1 this) (wpp2 this)) ->
      fs_entails
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp1)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp2).
      Proof. intros. eapply SMember_cast_mono; eauto. Qed.

    Lemma SMethodCast_mono_fupd cast wpp1 wpp2 :
      (∀ this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SMember_cast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp1)
        (SMember_cast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp2).
    Proof. exact: SMethodOptCast_mono_fupd. Qed.

    Lemma SMethod_mono_fupd wpp1 wpp2 :
      (∀ this, wpspec_entails_fupd (wpp1 this) (wpp2 this)) ->
      fs_entails_fupd
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp1)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp2).
    Proof. exact: SMethodOptCast_mono_fupd. Qed.

    #[local] Lemma SMethodOptCast_wpspec_monoN
        c wpp1 wpp2 vs K n :
      (∀ this, wpspec_entailsN n (wpp1 this) (wpp2 this)) ->
      member_to_function_spec c wpp2 vs K ⊢{n}
      member_to_function_spec c wpp1 vs K.
    Proof.
      move=>Hwpp /=. rewrite /exact_spec. f_equiv=>this.
      rewrite -(app_nil_l [_]) !arg_ok.
      repeat f_equiv. apply Hwpp.
    Qed.

    Lemma SMethodCast_ne cast wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp1 ≡{n}≡
      SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp2.
    Proof. exact: SMember_cast_ne. Qed.

    Lemma SMethod_ne wpp1 wpp2 n :
      (∀ this, wpspec_dist n (wpp1 this) (wpp2 this)) ->
      SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp1 ≡{n}≡
      SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp2.
    Proof. exact: SMember_cast_ne. Qed.

   Lemma SMethodCast_proper cast wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp1 ≡
      SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar) wpp2.
    Proof. exact: SMember_cast_proper. Qed.
    Lemma SMethod_proper wpp1 wpp2 :
      (∀ this, wpspec_equiv (wpp1 this) (wpp2 this)) ->
      SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp1 ≡
      SMethod (cc:=cc) class qual rq ret targs (ar:=ar) wpp2.
    Proof. exact: SMember_cast_proper. Qed.

    #[global] Instance: Params (@SMethodCast) 9 := {}.
    #[global] Instance: Params (@SMethod) 8 := {}.
    #[global] Instance SMethodCast_ne' cast n :
      Proper (dist (A:=ptr -d> WithPrePostO mpredI) n ==> dist n)
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_ne. Qed.
    #[global] Instance SMethod_ne' n :
      Proper (dist (A:=ptr -d> WithPrePostO mpredI) n ==> dist n)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_ne. Qed.

    #[global] Instance SMethodCast_proper' cast :
      Proper (equiv (A:=ptr -d> WithPrePostO mpredI) ==> equiv)
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar)).
    Proof. exact: ne_proper. Qed.
    #[global] Instance SMethod_proper' :
      Proper (equiv (A:=ptr -d> WithPrePostO mpredI) ==> equiv)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar)).
    Proof. exact: ne_proper. Qed.

    #[global] Instance SMethodCast_mono' cast :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_mono' :
      Proper (pointwise_relation _ wpspec_entails ==> fs_entails)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono. Qed.

    #[global] Instance SMethodCast_flip_mono' cast :
      Proper (flip (pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono. Qed.
    #[global] Instance SMethod_flip_mono' :
      Proper (flip (pointwise_relation _ wpspec_entails) ==> flip fs_entails)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono. Qed.

    #[global] Instance SMethodCast_mono_fupd' cast :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono_fupd. Qed.
    #[global] Instance SMethod_mono_fupd' :
      Proper (pointwise_relation _ wpspec_entails_fupd ==> fs_entails_fupd)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono_fupd. Qed.

    #[global] Instance SMethodCast_flip_mono_fupd' cast :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SMethodCast (cc:=cc) class cast qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethodCast_mono_fupd. Qed.
    #[global] Instance SMethod_flip_mono_fupd' :
      Proper (flip (pointwise_relation _ wpspec_entails_fupd) ==> flip fs_entails_fupd)
        (SMethod (cc:=cc) class qual rq ret targs (ar:=ar)).
    Proof. repeat intro. by apply SMethod_mono_fupd. Qed.
  End SMethod.

End with_cpp.
