(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.numbers.

(* TODO: the name here probably does not make sense anymore *)
Module CV.

  #[projections(primitive)]
  Record t : Set := mk { is_const : bool ; frac : Qp }.
  Coercion frac : t >-> Qp.

  Definition add (a b : t) : t :=
    mk (a.(is_const) || b.(is_const)) (a.(frac) + b.(frac)).

  Lemma eta q : q = mk (is_const q) (frac q).
  Proof. done. Qed.

  Lemma refl c q_f : mk c q_f = mk c q_f.
  Proof. done. Qed.

  (* we need a definition in order to make a coercion *)
  Definition _mut : Qp -> t := mk false.

  (* Notations -- probably actually make these notations? *)
  Notation mut := (mk false) (only parsing).
  Notation const := (mk true) (only parsing).
  Notation c := (mk true).
  Notation m := (mk false).

End CV.

Add Printing Constructor CV.t.
#[global] Bind Scope Qp_scope with CV.t.

(* as with C++, we make mutable the default *)
#[global] Coercion CV._mut : Qp >-> CV.t.

Section TEST.
  Variable TEST : CV.t -> CV.t -> CV.t -> CV.t -> Prop.

  (* TODO: to make this work without the [%Qp], we need to register the
     notations for [Qp] as notations in [cvq_scope]. *)
  Goal TEST 1 (CV.c 1) (1/2) (CV.c (1/4)).
  Abort.

End TEST.
