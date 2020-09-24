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
Require Import bedrock.lang.cpp.logic.destructors.

Require Import bedrock.lang.cpp.heap_notations.

Set Default Proof Using "Type".

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.
  Variable (ti : thread_info).

  Local Notation _sub := (_sub (resolve:=σ)) (only parsing).
  Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
  Local Notation _global := (_global (resolve:=σ)) (only parsing).

  (* this destructs an object by invoking its destructor
     note: it does *not* free the underlying memory.
   *)
  Definition destruct_obj (cls : globname) (v : val) (Q : mpred) : mpred :=
    match σ.(genv_tu) !! cls with
    | Some (Gstruct s) =>
      match s.(s_dtor) with
      | DtorDeleted => False
      | DtorUser nm =>
        match σ.(genv_tu).(symbols) !! nm with
        | None => False
        | Some ov =>
          let ty := type_of_value ov in
        if s.(s_virtual_dtor) then
          resolve_virtual (σ:=σ) (_eqv v) cls nm (fun da p =>
             |> fspec σ.(genv_tu).(globals) ty ti (Vptr da) (Vptr p :: nil) (fun _ => Q))
        else
           Exists da, _global nm &~ da **
                              |> fspec σ.(genv_tu).(globals) ty ti (Vptr da) (v :: nil) (fun _ => Q)
        end
      | DtorDefault =>
        destructors.wp_dtor (σ:=σ) ti (Tnamed cls) (_eqv v) Q
      end
    | _ => False
    end.

  (* [destruct_val t this dtor Q] invokes the destructor ([dtor]) on [this]
     with the type of [this] is [t].

     note: it does *not* free the underlying memory.
   *)
  Fixpoint destruct_val (t : type) (this : val) (Q : mpred)
           {struct t}
  : mpred :=
    match t with
    | Tqualified _ t => destruct_val t this Q
    | Tnamed cls =>
      destruct_obj cls this Q
    | Tarray t sz =>
      fold_right (fun i Q =>
         Exists p, _offsetL (_sub t (Z.of_nat i)) (_eqv this) &~ p ** destruct_val t (Vptr p) Q) Q (List.rev (seq 0 (N.to_nat sz)))
    | _ => emp
    end.

End destroy.
