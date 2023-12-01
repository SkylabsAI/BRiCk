(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
This file axiomatizes and instantiates [mpred] with the ghost types of the logic
that we use for C++.
The core C++ logic is defined in [pred.v]. *)
From iris.base_logic.lib Require Import own cancelable_invariants.
Require Import iris.bi.monpred.

From bedrock.prelude Require Import base.
From bedrock.lang Require Import bi.prelude.
Require Export bedrock.lang.base_logic.mpred.
Import ChargeNotation.

Module Type CPP_LOGIC_CLASS_BASE.
  Parameter cppG : gFunctors -> Type.
  Axiom has_inv : forall Σ, cppG Σ -> invGS Σ.
  Axiom has_cinv : forall Σ, cppG Σ -> cinvG Σ.

  Parameter _cpp_ghost : Type.
End CPP_LOGIC_CLASS_BASE.

Module Type CPP_LOGIC_CLASS_MIXIN (Import CC : CPP_LOGIC_CLASS_BASE).

  Definition cpp_preGS Σ thread_info : LOGIC.GpreS Σ thread_info := {|
    LOGIC.preGS := cppG Σ
  ; LOGIC.preGS_has_inv := has_inv Σ
  ; LOGIC.preGS_has_cinv := has_cinv Σ
  |}.
  Definition cpp_GS Σ thread_info : LOGIC.GS Σ thread_info := {|
    LOGIC.GS_pre := cpp_preGS Σ thread_info
  ; LOGIC.GS_ghost := _cpp_ghost
  |}.

  Class cpp_logic {thread_info : biIndex} : Type :=
  { cpp_Σ       : gFunctors
  ; cpp_ghost   : _cpp_ghost
  ; cpp_has_cppG : cppG cpp_Σ
  }.
  #[global] Arguments cpp_logic : clear implicits.

  (* Coercing cpp_logic to LOGIC.logic *)
  #[global] Instance cpp_logic_logic `{Σ : cpp_logic thread_info} : LOGIC.logic thread_info := {|
    LOGIC._Σ := cpp_Σ
  ; LOGIC._ghost_type := cpp_GS cpp_Σ thread_info
  ; LOGIC._ghost := cpp_ghost
  ; LOGIC._has_G := cpp_has_cppG
  |}.
  Coercion cpp_logic_logic : cpp_logic >-> LOGIC.logic.
  #[global] Hint Opaque cpp_logic_logic : typeclass_instances br_opacity.

End CPP_LOGIC_CLASS_MIXIN.

Module Type CPP_LOGIC_CLASS := CPP_LOGIC_CLASS_BASE <+ CPP_LOGIC_CLASS_MIXIN.

Declare Module LC : CPP_LOGIC_CLASS.
Export LC.
