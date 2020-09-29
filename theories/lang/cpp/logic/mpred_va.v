(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.bi Require Import bi monpred.
From iris.proofmode Require Import tactics.

From bedrock.lang.cpp.logic Require Import pred mpred.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Definition paddr := N.
Definition vaddr := N.
Definition byte := N.
Definition pdname := N.

Definition ASID : biIndex := BiIndex pdname _ eq _.

(** We are fixing that thread_info has 3 components, and the first component is
  ASID. The other 2 components (K and H) remain abstract in this file. They will
  be instantiated as the view for cache-effects of weak memory, and the view for
  TLBs from cache-effects of the address translation. *)

Module CPP_PHYSICAL.

Section with_cpp.
  Context {K H : biIndex}.

  Notation thread_info := (ASID *i K *i H).
  Notation L_ASID := (Lid.l : MLens thread_info ASID).
  Notation L_OTHER := (Lid.r : MLens thread_info (K *i H)).

  Context `{Σ : cpp_logic thread_info}.

  Parameter byte_at : forall (pa:paddr) (q : Qp) (v : byte), mpred.

  (* Non-TLB assumption. When TLBs come into play, [page_mappped] will depend on
    the TLB state. *)
  Parameter page_mapped :
    forall (γ : pdname) (va : vaddr) (q : Qp) (pa : paddr), (iPropI Σ).

  (* Physical bytes should not depend on the address space *)
  Axiom byte_at_objective_with_asid :
    forall pa q v, ObjectiveWith L_ASID (byte_at pa q v).

  (* SC assumption. In weak memory, [byte_at] will NOT be objective w.r.t thread
    views. *)
  Axiom byte_at_objective_with_other :
    forall pa q v, ObjectiveWith L_OTHER (byte_at pa q v).

  Global Existing Instances byte_at_objective_with_asid
                            byte_at_objective_with_other.
End with_cpp.
End CPP_PHYSICAL.

Module ASID_THEORY.
Include CPP_PHYSICAL.
Section with_cpp.
  Context {K H : biIndex}.

  Notation thread_info := (ASID *i K *i H).
  Notation L_ASID := (Lid.l : MLens thread_info ASID).
  Notation L_OTHER := (Lid.r : MLens thread_info (K *i H)).

  Context `{Σ : cpp_logic thread_info}.

  Implicit Types (q : Qp) (va : vaddr) (pa : paddr).
  Definition page_mapping' va q pa : monPred ASID (iPropI Σ) :=
    @MonPred ASID _ (fun γ => page_mapped γ va q pa)%I _.

  Definition page_mapping va q pa : mpred :=
    monPred2_embed L_ASID (page_mapping' va q pa).

  Definition vbyte va (v: byte) q : mpred :=
    Exists pa, byte_at pa q v ** page_mapping va q pa.

  Instance page_mapping_objective_with_other va q pa :
    ObjectiveWith L_OTHER (page_mapping va q pa).
  Proof. apply _. Qed.

  Instance page_mapping_exactly_with_objective_with :
    Objective (@(L_ASID, asid) (page_mapping va q pa)).
  Proof. apply _. Qed.

  Instance vbyte_objective_with_other va v q :
    ObjectiveWith L_OTHER (vbyte va v q).
  Proof. apply _. Qed.
End with_cpp.
End ASID_THEORY.
