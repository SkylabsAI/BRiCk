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

Local Notation vaddr := N.
Local Notation byte := N.

Definition ASID : biIndex := {|
  bi_index_type := vaddr
; bi_index_rel := eq
|}.

Section asid_bi.
  Context {K H : biIndex}.

  Notation thread_info := (ASID *i K *i H).
  Notation L_ASID := (Lid.l : MLens thread_info ASID).
  Notation L_OTHER := (Lid.r : MLens thread_info (K *i H)).

  Context `{Σ : cpp_logic thread_info}.

  Definition vbyte' (va : vaddr) (v: byte) : monPred ASID (iPropI Σ) :=
    MonPred (fun asid => emp)%I _.
  Definition vbyte (va : vaddr) (v: byte) : mpred :=
    monPred_embed L_ASID (vbyte' va v).

  Lemma vbyte_objective_with_other va v : ObjectiveWith L_OTHER (vbyte va v).
  Proof.
  Admitted.

  Instance : Objective (@(L_ASID, asid) (vbyte va v)).
  Proof.
    intros. apply monPred_objective_with_id_objective.
    apply monPred_exactly_with_objective_with_left.
    apply vbyte_objective_with_other.
  Qed.
End asid_bi.