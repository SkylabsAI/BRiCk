(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.ZArith.ZArith.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred wp path_pred heap_pred.
Require Import bedrock.lang.cpp.logic.dispatch.

Require Import bedrock.lang.cpp.heap_notations.

Set Default Proof Using "Type".

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.
  Variable (ti : thread_info).

  Local Notation _sub := (_sub (resolve:=σ)) (only parsing).
  Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
  Local Notation _global := (_global (resolve:=σ)) (only parsing).

  (* TODO: move? *)
  Instance fold_left_ne {T : ofeT} {U : Type} {n} :
    Proper ((dist n ==> pointwise_relation _ (dist n)) ==> eq ==> dist n ==> dist n) (@fold_left T U).
  Proof.
    do 4 red; intros f1 f2 Hf xs1 _ <-.
    induction xs1; simpl; first done.
    intros x1 x2 Hx.
    eapply IHxs1, Hf, Hx.
  Qed.

  Fixpoint all_identities' (f : nat) (mdc : option globname) (cls : globname) : Rep :=
    match f with
    | 0 => lfalse
    | S f =>
      match σ.(genv_tu).(globals) !! cls with
      | Some (Gstruct st) =>
        _identity σ cls mdc 1 **
        [∗list] b ∈ st.(s_bases),
           let '(base,_) := b in
           _base σ cls base |-> all_identities' f mdc base
      | _ => False
      end
    end%I.

  Definition all_identities : option globname -> globname -> Rep :=
    let size := avl.IM.cardinal σ.(genv_tu).(globals) in
    (* ^ the number of global entries is an upper bound on the height of the
       derivation tree.
     *)
    all_identities' size.

  (** [revert_identities cls Q] destroys the identity of [cls] that lives at [this].
      In doing so, it updates the identities of all base classes to have each base
      be its own "most-derived-class".

      This is necessary to make virtual dispatch work correctly when base classes
      are destroyed.
   *)
  Definition revert_identity (cls : globname) (Q : mpred) : Rep :=
    match σ.(genv_tu).(globals) !! cls with
    | Some (Gstruct st) =>
      _identity σ cls (Some cls) 1 **
      ([∗list] b ∈ st.(s_bases),
          let '(base,_) := b in
          _base σ cls base |-> all_identities (Some cls) base) **
      (_identity σ cls None 1 -*
       ([∗list] b ∈ st.(s_bases),
         let '(base,_) := b in
         _base σ cls base |-> all_identities (Some base) base) -* pureR Q)
    | _ => False
    end%I.

  Instance revert_identity_ne : Proper (dist n ==> dist n) (revert_identity cls).
  Proof.
    red. red. rewrite /revert_identity; intros.
    repeat case_match =>//.
    solve_proper.
  Qed.

  Unset Program Cases.

  Program Definition wp_default_dtor_pre (destruct_type : type -d> Loc -d> mpredI -n> mpredI)
    : globname -d> Struct -d> Loc -d> mpredI -n> mpredI :=
    λ cls st this, λne Q,
    let bases :=
        fold_left (fun Q '(base, _) =>
                     |> destruct_type (Tnamed base) (_offsetL (_base σ cls base) this) Q) st.(s_bases) Q
    in
    let ident := this |-> revert_identity cls bases in
    fold_left (fun Q '(x,ty,_,_) =>
                 match drop_qualifiers ty with
                 | Tnamed nm =>
                   let l' := _offsetL (_field (resolve:=σ) {| f_type := cls ; f_name := x |}) this  in
                   |> destruct_type ty l' Q
                 | _ => Q
                 end) st.(s_fields) ident.
  Next Obligation.
    intros ? ? ? ? ? ? ? ?; simpl.
    apply fold_left_ne; eauto.
    { intros ? ? ? ?; repeat case_match =>/=; eauto.
      rewrite H0. reflexivity. }
    { apply _at_ne. apply revert_identity_ne.
      apply fold_left_ne; try done.
      do 4 intro; repeat case_match => //; subst; f_contractive.
      apply ofe_mor_car_ne, dist_S; eauto. }
  Qed.

  Instance wp_default_dtor_contractive : Contractive wp_default_dtor_pre.
  Proof.
    intros n f1 f2 Hf cls st this Q.
    unfold wp_default_dtor_pre; simpl.
    apply fold_left_ne; eauto.
    { intros ? ? ? ?; repeat case_match => /=; eauto.
      rewrite H.
      f_contractive. eapply Hf. }
    apply _at_ne. apply revert_identity_ne.
    apply fold_left_ne; try done.
    do 4 intro; repeat case_match => /=. rewrite H. f_contractive. apply Hf.
  Qed.

  Program Definition wp_dtor_pre (destruct_type : type -d> Loc -d> mpredI -n> mpredI)
    : type -d> Loc -d> mpredI -n> mpredI :=
    λ t this, λne Q,
       match drop_qualifiers t with
       | Tnamed cls =>
         match σ.(genv_tu).(globals) !! cls with
         | Some (Gstruct st) =>
           match st.(s_dtor) with
           | DtorDeleted => False
           | DtorUser nm =>
             match σ.(genv_tu).(symbols) !! nm with
             | Some (Odestructor d) =>
               let dt := type_of_value (Odestructor d) in
              Exists da thisp, _global nm &~ da ** this &~ thisp **
                                        |> fspec σ.(genv_tu).(globals) dt ti (Vptr da) (Vptr thisp :: nil) (fun _ => Q)
             | _ => False
             end
           | DtorDefault =>
             wp_default_dtor_pre destruct_type cls st this Q
           end
         | Some (Gunion _) =>
           (* Unions are variant types and they are *not* destructed.
              See http://eel.is/c++draft/class.dtor#14
              "After executing the body of the destructor ... a destructor for
               class X calls the destructors for X's direct **non-variant**
               non-static data members, the destructors for X's non-virtual
               direct base classes and,..."
            *)
           Q
         | Some (Genum t _) => |> destruct_type t this Q
         | _ => False
         end
       | Tarray ty n =>
         (* destroy an array by destroying each element starting from the end *)
         List.fold_left (fun Q off =>
                           |> destruct_type ty (this ., (_sub ty (Z.of_nat off))) Q) (seq 0 (N.to_nat n)) Q
       | Tptr _ | Tref _ | Trv_ref _
       | Tint _ _ | Tfunction _ _ | Tbool | Tmember_pointer _ _ | Tfloat _
       | Tnullptr | Tarch _ _ => Q

       | Tqualified _ _ | Tvoid => False
       end%I.
  Next Obligation.
    intros wp_dtor t this n Q1 Q2 HQ.
    simpl.
    repeat case_match; try fast_done; first last. {
      f_contractive.
      by apply ofe_mor_car_ne, dist_S, HQ.
    }
    by repeat f_equiv.
    apply wp_default_dtor_pre; eauto.
    apply fold_left_ne; try done.
    do 4 intro. rewrite H. eauto.
  Qed.

  Instance wp_dtor_pre_contractive : Contractive wp_dtor_pre.
  Proof.
    intros n f1 f2 Hf t this Q.
    unfold wp_dtor_pre; simpl.
    repeat case_match; try fast_done; first last. {
      f_contractive.
      apply Hf.
    }
    eapply wp_default_dtor_contractive; eauto.
    apply fold_left_ne; try done.
    do 4 intro. rewrite H. f_contractive. apply Hf.
  Qed.

  (** [wp_dtor ty this Q] represents the weakest pre-condition for invoking the
      destructor for the type [ty] on the location [this] with post-condition [Q].

      Note that this is like the weakest pre-condition for a function, it does
      perform virtual dispatch.
   *)
  Definition wp_dtor : type -d> Loc -d> mpredI -n> mpredI :=
    fixpoint wp_dtor_pre.

  Lemma wp_dtor_unfold : wp_dtor ≡ wp_dtor_pre wp_dtor.
  Proof. apply fixpoint_unfold. Qed.

  Lemma wp_dtor_unfold_eta t this Q : wp_dtor t this Q ≡ wp_dtor_pre wp_dtor t this Q.
  Proof. apply wp_dtor_unfold. Qed.

  Definition wp_default_dtor := wp_default_dtor_pre wp_dtor.

End destroy.
