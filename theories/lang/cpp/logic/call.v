(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp wp_rep destroy initializers.
Require Import bedrock.lang.cpp.heap_notations.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Local Notation wp_lval := (wp_lval (resolve:=σ) M ti ρ).
  Local Notation wp_prval := (wp_prval (σ:=σ) M ti ρ).
  Local Notation wp_xval := (wp_xval (resolve:=σ) M ti ρ).

  (** TODO [Q] could be [list ptr -> FreeTemps -> mpred] *)
  Fixpoint wp_args (ts : list type) (es : list Expr) (Q : list ptr -> FreeTemps -> mpred)
  : mpred :=
    match ts , es with
    | nil , nil => Q nil emp%I
    | t :: ts , e :: es =>
      wp_auto_alloc ti t (fun p free =>
        Exists (Qarg : FreeTemps -> mpred),
        wp_initialize M ti ρ t p e Qarg **
        wp_args ts es (fun vs frees =>
                         Forall free,
                         Qarg free -* Q (p :: vs) (free ** frees)))
    | _ , _ => False (* mismatched arguments and parameters. *)
    end.

  Lemma wp_args_frame_strong : forall ts es Q Q',
      (Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free) |-- wp_args ts es Q -* wp_args ts es Q'.
  Proof.
    elim; destruct es => /=; try solve [ by intros; iIntros "? []" ].
    { by iIntros (? ?) "H"; iApply "H". }
    { rewrite /wp_auto_alloc/wp_alloc.
      iIntros (? ?) "H K"; iIntros (?) "at".
      iDestruct ("K" with "at") as (Qarg) "K".
      iExists _.
      iDestruct "K" as "[$ K]".
      iRevert "K"; iApply H.
      iIntros (?? ?) "X"; iIntros (?) "Qarg".
      iApply "H"; first by simpl; eauto. by iApply "X". }
  Qed.

  Lemma wp_args_frame : forall ts es Q Q',
      (Forall vs free, Q vs free -* Q' vs free) |-- wp_args ts es Q -* wp_args ts es Q'.
  Proof.
    intros; iIntros "X".
    iApply wp_args_frame_strong.
      by iIntros (vs free) "% H"; iApply "X".
  Qed.

End with_resolve.
