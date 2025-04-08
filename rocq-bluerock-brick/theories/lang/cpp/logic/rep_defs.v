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
Implicit Types (σ : genv).

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

Structure tagged_lhs := TagLHS { #[reversible=no] untag_lhs :> Type }.
Definition offset_lhs_tag ty := TagLHS ty.
Canonical ptr_lhs_tag ty := offset_lhs_tag ty.

Structure tagged_res := TagRES { #[reversible=no] untag_res :> Type }.
Definition offset_res_tag ty := TagRES ty.
Canonical ptr_res_tag ty := offset_res_tag ty.

(* points-to *)
#[projections(primitive=yes)]
Structure AT `{Σ : cpp_logic} : Type :=
  { #[canonical=yes] AT_LHS :> tagged_lhs
  (** ^^ We make [AT_LHS] a coercion *)
  ; #[canonical=yes] AT_Result : tagged_res
  (* We hardcode [Rep] as second argument to improve error messages *)
  ; #[canonical=no] AT_at : AT_LHS -> Rep -> AT_Result }.
#[global] Arguments AT_at {AT} _ _ _ : rename, simpl never.

mlock Definition __at := @AT_at.
#[global] Arguments __at {ti Σ0 Σ AT} _ _ : rename.

(** Since this will appear in inferred types, we choose meaningful names. This
naming choice makes [ptrA] seem an alternative spelling of [ptr] (like [mpred]
and [mpredI], and similarly for [offsetA]. *)
Canonical Structure ptrA `{Σ : cpp_logic} : AT :=
  {| AT_LHS := ptr_lhs_tag ptr; AT_Result := ptr_res_tag mpred; AT_at := at_aux |}.
Canonical Structure offsetA `{Σ : cpp_logic} : AT :=
  {| AT_LHS := offset_lhs_tag offset; AT_Result := offset_res_tag Rep; AT_at := offsetR_aux |}.

Module DELETEME.
  Section Tests.
    Context `{cpp_logic}.
    (* Make sure there are no implicit types. *)
    Fail Example no_implicit_offset := fun o => o.
    Fail Example no_implicit_offset := fun p => p.
    Example ex1 := fun p R => __at p R |-- False.
    Check ex1 : forall (p : ptr), _. (* make sure it's [ptr] by default. *)
    Example ex2 := fun (p : ptr) R => __at p R |-- False.    (* explicit annotations work, of course. *)
    Example ex3 := fun (o : offset) R => __at o R |-- False. (* explicit annotations work, of course. *)
    Example ex4 := fun o R => __at o R |-@{Rep} False.       (* expected types also help pick the right instance *)
    Check ex4 : forall (o : offset), _.
    Example ex5 := fun o R => __at o R |-@{mpred} False.     (* expected types also help pick the right instance *)
    Check ex5 : forall (o : ptr), _.
  End Tests.
End DELETEME.

(** [_at base R] states that [R base] holds.

    NOTE This is "weakly at"
  *)
#[global] Notation _at := (__at (AT := ptrA)).
#[global] Notation _offsetR := (__at (AT := offsetA)).
(**
The above notations are used for printing [_at] / [_offset] in the few cases
where they are partially applied.

[_ |-> _] is preferred because declared later.
 *)

#[global] Notation "p |-> r" := (__at p r)
  (at level 15, r at level 20, right associativity) : stdpp_scope.

Module INTERNAL.
  Ltac unfold_at := rewrite __at.unlock /AT_at/(AT_at _ _ _ _)/= 1?at_aux.unlock 1?offsetR_aux.unlock.
  Lemma _at_eq `{Σ : cpp_logic} p R : p |-> R = R.(monPred_at) p.
  Proof. by unfold_at. Qed.
  Lemma _offsetR_eq `{Σ : cpp_logic} o R : o |-> R =
    as_Rep (fun p => R.(monPred_at) (p ,, o)).
  Proof. by unfold_at. Qed.
End INTERNAL.
