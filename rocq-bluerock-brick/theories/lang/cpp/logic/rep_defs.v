(*
 * Copyright (c) 2020-21 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Most clients should import [bluerock.lang.cpp.logic.rep] instead of this file.
This file defines the core type [Rep] of representation predicates.
TODO: merge back into [rep.v]?
*)
Require Import elpi.apps.locker.locker.
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.bi.monpred.
Require Import bluerock.lang.cpp.semantics.values.
Require Import bluerock.lang.cpp.logic.mpred.

Import ChargeNotation.
Implicit Types (σ : genv) (o : offset).

(** Representation predicates are implicitly indexed by a location, and should be used to
  * assert properties of the heap
  *)
Canonical Structure ptr_bi_index : biIndex :=
  BiIndex ptr _ eq _.

#[global] Instance ptr_bi_index_discrete : BiIndexDiscrete ptr_bi_index.
Proof. by move=>i i'. Qed.

(** The tactic [intros ->%ptr_rel_elim] is much faster than [intros
    ->] when introducing [p1 ⊑ p2] (when the latter works at all). *)
Lemma ptr_rel_elim (p1 p2 : ptr) : p1 ⊑ p2 → p1 = p2.
Proof. done. Qed.

Canonical Structure RepI `{!cpp_logic thread_info Σ} :=
  monPredI ptr_bi_index (@mpredI thread_info Σ).
Definition Rep `{Σ : cpp_logic} : Type := RepI.
Definition RepO `{Σ : cpp_logic} : ofe := RepI.

#[global] Bind Scope bi_scope with Rep.

Section defs.
  Context `{Σ : cpp_logic}.

  Definition as_Rep (P : ptr -> mpred) : Rep := MonPred P _.

  (* todo(gmm): make opaque *)
  Definition pureR (P : mpred) : Rep :=
    as_Rep (fun _ => P).
End defs.
#[global] Instance: Params (@as_Rep) 3 := {}.
#[global] Instance: Params (@pureR) 3 := {}.

mlock Definition at_aux `{Σ : cpp_logic} (p : ptr) (R : Rep) : mpred :=
  R.(monPred_at) p.

mlock Definition offsetR_aux `{Σ : cpp_logic} (o : offset) (R : Rep) : Rep :=
  as_Rep (fun base => R.(monPred_at) (base ,, o)).

(* TODO replace by the right instances. *)
#[global] Instance: Params (@at_aux) 4 := {}.
#[global] Instance: Params (@offsetR_aux) 4 := {}.

(* points-to *)
#[projections(primitive=yes)]
Class At `{Σ : cpp_logic} (LHS : Type) (Result : bi) := MkAt {
  __at : LHS -> Rep -> Result
}.
#[global] Hint Opaque __at : br_opacity typeclass_instances.
#[global] Arguments __at : simpl never.
#[global] Arguments __at {_ _ _ _ _ _} _ _ : assert.

(** Since this will appear in inferred types, we choose meaningful names. This
naming choice makes [ptrA] seem an alternative spelling of [ptr] (like [mpred]
and [mpredI], and similarly for [offsetA]. *)
#[global] Instance ptrA `{Σ : cpp_logic} : At ptr mpredI :=
  {| __at := at_aux |}.
#[global] Instance offsetA `{Σ : cpp_logic} : At offset RepI :=
  {| __at := offsetR_aux |}.

(** [_at base R] states that [R base] holds.

    NOTE This is "weakly at"
  *)
#[global] Notation _at := (__at (At := ptrA)).
#[global] Notation _offsetR := (__at (At := offsetA)).
(**
The above notations are used for printing [_at] / [_offset] in the few cases
where they are partially applied.

[_ |-> _] is preferred because declared later.
 *)

#[global] Notation "p |-> r" := (__at p r)
  (at level 15, r at level 20, right associativity) : stdpp_scope.

Module INTERNAL.
  Ltac unfold_at := rewrite /__at/= 1?at_aux.unlock 1?offsetR_aux.unlock.
  Lemma _at_eq `{Σ : cpp_logic} p R : p |-> R = R.(monPred_at) p.
  Proof. by unfold_at. Qed.
  Lemma _offsetR_eq `{Σ : cpp_logic} o R : o |-> R =
    as_Rep (fun p => R.(monPred_at) (p ,, o)).
  Proof. by unfold_at. Qed.
End INTERNAL.

Module Type UNIT.
End UNIT.

Module TEST (U : UNIT).

  Definition rev_lookup `{Countable K} `{EqDecision V} (m : gmap K V) (v : V) : option K.
  Admitted.

  Section inference_test.
    Context `{Σ : cpp_logic}.

    Goal ∀ (R : Rep), ⊢@{mpredI} Exists p, p |-> R.
    (**
    forall R : @Rep thread_info _Σ Σ,
    @bi_emp_valid (@mpredI thread_info _Σ)
      (@bi_exist (AT_bi (@AT_Result _ _ _ (@ptrA thread_info _Σ Σ))) (@AT_LHS _ _ _ (@ptrA thread_info _Σ Σ))
        (fun p : @AT_LHS _ _ _ (@ptrA thread_info _Σ Σ) => @__at.body thread_info _Σ Σ (@ptrA thread_info _Σ Σ) p R))

    forall R : @Rep thread_info _Σ Σ,
    @bi_emp_valid (@mpredI thread_info _Σ)
      (@bi_exist (@mpredI thread_info _Σ) ptr (fun p : ptr => @__at _ _ _ _ _ (@ptrA thread_info _Σ Σ) p R))

    Goal ∀ (R : Rep) (σ : genv) f, ⊢@{mpredI} Exists p, p ,, o_field _ f |-> R.
    Goal ∀ (R : Rep) (σ : genv) f p,
      ⊢@{mpredI} p ,, o_field _ f ,, o_field σ f |-> R.
    Proof.
      simpl.

    *)
    Abort.

    Fail Goal ∀ (R : Rep) (σ : genv) f p,
      ⊢@{mpredI} p ,, o_field _ f ,, o_field σ f |-> R.
    Goal ∀ (R : Rep) (σ : genv) f (p : ptr),
      ⊢@{mpredI} p ,, o_field _ f ,, o_field σ f |-> R.
    Proof.
      simpl.

    Abort.

    Fail Goal ∀ (R : Rep) (σ : genv) f p (m : gmap N _),
      rev_lookup m p = None ->
      ⊢@{mpredI} p ,, o_field _ f ,, o_field σ f |-> R.

    Goal ∀ (R : Rep) (σ : genv) f (p : ptr) (m : gmap N _),
      rev_lookup m p = None ->
      ⊢@{mpredI} p ,, o_field _ f ,, o_field σ f |-> R.
    Proof.
      simpl.

    Abort.
  End inference_test.
End TEST.
