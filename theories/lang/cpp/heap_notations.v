(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred.

Set Primitive Projections.

Coercion _eqv : val >-> ptr.

(* coercions to [offset], V2 bad *)
Definition rel_offset : Type := genv -> offset.
Coercion offset_to_rel_offset := const : offset -> rel_offset.
Coercion field_to_rel_offset := flip o_field : field -> rel_offset.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* coercions to [offset], V1 good *)
  Structure TO_OFFSET : Type :=
  { TO_OFFSET_from : Type
  ; TO_OFFSET_to : Type
  ; #[canonical=no] _to_offset {σ : genv} : TO_OFFSET_from -> TO_OFFSET_to
  }.
  Arguments _to_offset {!TO_OFFSET} _ : rename.

  Canonical Structure TO_OFFSET_field := {| TO_OFFSET_from := field; TO_OFFSET_to := offset; _to_offset := o_field |}.
  Canonical Structure TO_OFFSET_offset := {| TO_OFFSET_from := offset; TO_OFFSET_to := offset; _to_offset σ (o : offset) := o |}.
  Canonical Structure TO_OFFSET_ptr := {| TO_OFFSET_from := ptr; TO_OFFSET_to := ptr; _to_offset σ p := p |}.
  (* Canonical Structure TO_OFFSET_val := {| TO_OFFSET_from := val; TO_OFFSET_to := ptr; _to_offset σ := _eqv |}. *)

  (* "points to" *)
  Structure AT : Type :=
  { AT_lhs    : Type
  ; AT_rhs    : Type
  ; AT_result :> Type
  ; #[canonical=no] AT_at :> AT_lhs -> AT_rhs -> AT_result
  }.
  Arguments AT_at {!AT} _ _ : rename.

  Canonical Structure mpredA : AT :=
    {| AT_lhs := ptr; AT_rhs := Rep; AT_result := mpred; AT_at := _at |}.

  Canonical Structure RepA : AT :=
    {| AT_lhs := offset; AT_rhs := Rep; AT_result := Rep; AT_at o := _offsetR o |}.

  (* paths *)
  Structure DOT : Type :=
  { DOT_from : Type
  ; DOT_to : Type
  ; #[canonical=no] DOT_dot : offset -> DOT_from -> DOT_to
  }.
  Arguments DOT_dot {!AT} _ _ : rename.

  Canonical Structure DOT_offset_ptr : DOT :=
    {| DOT_from := ptr; DOT_to := ptr; DOT_dot o p := _offset_ptr p o |}.
  Canonical Structure DOT_offset_offset : DOT :=
    {| DOT_from := offset; DOT_to := offset; DOT_dot o1 o2 := o_dot o2 o1 |}.
End with_cpp.

(* notations *)
Notation "l |-> r" := (@AT_at _ l r)
  (at level 15, r at level 20, right associativity).

Notation "p ., o" := (@DOT_dot _ (_to_offset _ o) p)
  (at level 11, left associativity, format "p  .,  o").

Notation "p .[ t ! n ]" := (@DOT_dot _ (@o_sub _ t n%Z) p)
  (at level 11, left associativity, format "p  .[  t  '!'  n  ]").

Notation ".[ t ! n ]" := ((o_sub _ t n))
  (at level 11, format ".[  t  !  n  ]").

(* Test suite *)
Section test_suite.

  Context {σ : genv} `{Σ : cpp_logic} (R : Rep) (f g : field) (o : offset) (l : ptr) (p : ptr) (v : val).

  Example _0 := |> l |-> R.

  Example _1 := |> l ., f |-> R.

  Example _2 := l |-> f |-> R.

  Example _3 := l .[ T_int ! 0 ] |-> R.

  Example _4 := l |-> f .[ T_int ! 0 ] |-> R.

  Example _5 := l .[ T_int ! 0 ] .[ T_int ! 3 ] |-> R.

  Example _6 := l ., f .[ T_int ! 0 ] ., g |-> R.

  Example _7 := l ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> f |-> R.

  Example _8 := p ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> .[ T_int ! 1 ] |-> R.

  Example _9 := o ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> R.

  Example _10 := o ., g ., f .[ T_int ! 1 ] .[ T_int ! 0 ] ., f |-> R.

  Example _11 := o .[ T_int ! 1 ] |-> R.

  Example _12 := o .[ T_int ! 1 ] |-> R.

  Example _13 := v .[ T_int ! 1 ] |-> R.

  Example _14 := .[ T_int ! 1 ] |-> R.

  Example _15 := |> .[ T_int ! 1 ] |-> |> R.

  Fail Example _16 := l |-> ▷ R ∗ R.
  Fail Example _16 := l |-> |> R ** R. (* requires parsing as [(l |-> |> R) ** R] *)

  Fail Example _f := l |-> R ** R. (* requires parsing as [(l |-> R) ** R] *)

  Fail Example _BAD := l |-> R q.

End test_suite.
