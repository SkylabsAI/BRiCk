(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** * Auxiliary semantic definitions
 *)
Require Import bedrock.lang.prelude.base.

Require Import stdpp.coPset.
Require Import iris.bi.monpred.
From iris.proofmode Require Import tactics classes.

From bedrock.lang.cpp Require Import
     ast semantics logic.pred logic.rep logic.wp logic.heap_pred heap_notations destroy.

Set Primitive Projections.

(**
   This file defines derived concepts from the core [wp] rules in
   [logic.wp]. It is broken into a separate file due to the
   dependency on [destruct_val] (defined in [logic.destroy]).

   NOTE a better solution is to lift [destruct_val] higher up,
   since it only depends on function call semantics and not
   the syntax of programs.

   Most importantly, it defines rules around the constrution of
   temporary objects (which have ownership in our program logic).
 *)
Section contextualized.
  Context `{Σ : cpp_logic thread_info}.
  Context {σ : genv} (M : coPset) (ti : thread_info) (ρ : region).
  Implicit Types P : mpred.

  (** [wp_alloc ty Q] allocates storage for [ty] and passes the address
      to [Q]. Generally, [Q] will initialize this memory.
   *)
  Definition wp_alloc (ty : type) (Q : ptr -> mpred) : mpred :=
    Forall addr : ptr, addr |-> tblockR (erase_qualifiers ty) 1 -* Q addr.

  (** [wp_free ty addr Q] frees the memory of a [ty] at address [addr].
   *)
  Definition wp_free (ty : type) (addr : ptr) (Q : mpred) : mpred :=
    destruct_val ti false ty addr (addr |-> tblockR (σ:=σ) ty 1 ** Q).

  (** [wp_auto_alloc ty Q] allocates storage for [ty] and passes the address
      to [Q]. Generally, [Q] will initialize this memory.
   *)
  Definition wp_auto_alloc (ty : type) (Q : ptr -> FreeTemps -> mpred) : mpred :=
    wp_alloc ty (fun p => Q p (wp_free ty p emp)). (** TODO the use of [emp] here is concerning *)

  (** [wp_prval M ρ e Q] evaluate [e] and return a pointer to the (tempoary)
      location that stores the value.
      The second argument to [Q] is the temps that should be destroyed.
   *)
  Definition wp_prval (e : Expr) (Q : ptr -> FreeTemps -> epred) : mpred :=
    let ty := type_of e in
    wp_auto_alloc ty (fun p free => wp_init M ti ρ ty p e (fun free' => Q p (free ** free'))).

  (* [wp_operand M ρ e Q] evaluate [e] as the argument of an operator, i.e. to a [val].
     The second agument to [Q] is the temps that should be destroyed.
   *)
  Definition wp_operand (e : Expr) (Q : val -> FreeTemps -> epred) : mpred :=
    let rty := erase_qualifiers (type_of e) in
    wp_prval e (fun p free => Exists v, (Exists q, p |-> primR rty q v ** True) //\\ Q v free).

  (** [wpe vc e Q] evaluate [e] according to the value category [vc] *)
  Definition wpe (vc : ValCat) (e : Expr) (Q : ptr -> FreeTemps -> epred) : mpred :=
    match vc with
    | Xvalue => wp_xval M ti ρ e Q
    | Lvalue => wp_lval M ti ρ e Q
    | Prvalue => wp_prval e Q
    end.
End contextualized.

