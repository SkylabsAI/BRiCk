(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy initializers.
Require Import bedrock.lang.cpp.heap_notations.

Section with_resolve.
  Context `{Σ : cpp_logic} {σ : genv}.
  Variables (M : coPset) (ti : thread_info) (ρ : region).

  Local Notation wp_lval := (wp_lval (resolve:=σ) M ti ρ).
  Local Notation wp_prval := (wp_prval (resolve:=σ) M ti ρ).
  Local Notation wp_xval := (wp_xval (resolve:=σ) M ti ρ).

  (**
  [wp_args] encodes parameter passing as specified by the [standard](https://eel.is/c++draft/expr.call#7):
  > When a function is called, each parameter ([dcl.fct]) is initialized ([dcl.init], [class.copy.ctor])
  > with its corresponding argument.
  *)
  (** TODO [Q] could be [list ptr -> FreeTemps -> mpred] *)
  (**
  [wp_args] encodes parameter passing as specified by the [standard](https://eel.is/c++draft/expr.call#7):
  > When a function is called, each parameter ([dcl.fct]) is initialized ([dcl.init], [class.copy.ctor])
  > with its corresponding argument.
   *)
  Fixpoint wp_args' (ts : list type) (es : list Expr) (Q : list ptr -> list FreeTemps -> mpred)
  : mpred :=
    match ts , es with
    | nil , nil => Q nil nil
    | t :: ts , e :: es =>
      Forall a,
      Exists Qarg : FreeTemp -> FreeTemps -> mpred,
        wp_initialize M ti ρ false t a e Qarg **
        wp_args' ts es (fun ps frees =>
                         Forall free free',
                         Qarg free free' -* Q (a :: ps) ((free >*> free')%free :: frees))
    | _ , _ => False (* mismatched arguments and parameters. *)
    end.

  Lemma wp_args'_frame_strong : forall ts es Q Q',
      (Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free) |-- wp_args' ts es Q -* wp_args' ts es Q'.
  Proof.
    elim; destruct es => /=; try solve [ by intros; iIntros "? []" ].
    { by iIntros (? ?) "H"; iApply "H". }
    { iIntros (? ?) "H". iIntros "K" (p).
      iDestruct ("K" $! p) as (Qarg) "K".
      iExists _.
      iDestruct "K" as "[$ K]".
      iRevert "K"; iApply H.
      iIntros (?? ?) "X".
      iIntros (??) "f".
      iDestruct ("X" with "f") as "X".
      iRevert "X"; iApply "H".
      iPureIntro; simpl; eauto. }
  Qed.

  Definition pars := fold_right FreeTemps.par FreeTemps.id.

  #[program] Definition wp_args (ts : list type) (es : list Expr) (Q : list ptr -> FreeTemps -> mpred) : mpred :=
    wp_args' ts es (fun ps (frees : list FreeTemps.t) => Q ps (pars frees)).

  Lemma wp_args_frame_strong : forall ts es Q Q',
      (Forall vs free, [| length vs = length es |] -* Q vs free -* Q' vs free) |-- wp_args ts es Q -* wp_args ts es Q'.
  Proof.
    intros. iIntros "X"; iApply wp_args'_frame_strong.
    iIntros (??) "?". by iApply "X".
  Qed.

  Lemma wp_args_frame : forall ts es Q Q',
      (Forall vs free, Q vs free -* Q' vs free) |-- wp_args ts es Q -* wp_args ts es Q'.
  Proof.
    intros; iIntros "X".
    iApply wp_args_frame_strong.
      by iIntros (vs free) "% H"; iApply "X".
  Qed.

End with_resolve.
