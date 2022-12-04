(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.numbers.


Declare Scope cvq_scope.
Delimit Scope cvq_scope with cvq.

Module CV.

  Record t : Set := mk { is_const : bool ; is_volatile : bool ; frac : Qp }.
  Add Printing Constructor t.
  Bind Scope cvq_scope with t.
  Coercion frac : t >-> Qp.

  Definition add (a b : t) : t :=
    mk (a.(is_const) || b.(is_const)) (a.(is_volatile) || b.(is_volatile))
       (a.(frac) + b.(frac)).

  Lemma eta q : q = mk (is_const q) (is_volatile q) (frac q).
  Proof. by destruct q; intros. Qed.

  Lemma refl v c q_f : mk v c q_f = mk v c q_f.
  Proof. done. Qed.

  (* Notations -- probably actually make these notations? *)
  Definition mut : Qp -> t := mk false false.
  Definition const : Qp -> t := mk true false.
  Definition volatile : Qp -> t := mk false true.
  Definition const_volatile : Qp -> t := mk true true.

  Notation c := const.
  Notation v := volatile.
  Notation cv := const_volatile.
  Notation vc := const_volatile (only parsing).
  Notation m := mut.

End CV.

(* as with C++, we make mutable the default *)
#[global] Coercion CV.mut : Qp >-> CV.t.

Module Type TEST.
  Variable TEST : CV.t -> CV.t -> CV.t -> CV.t -> Prop.

  (* TODO: to make this work without the [%Qp], we need to register the
     notations for [Qp] as notations in [cvq_scope]. *)
  Goal TEST 1%Qp (CV.c 1) (CV.v 1) (CV.cv 1).
  Abort.

End TEST.
(*
#[global] Notation Qp_plain := stdpp.numbers.Qp.
#[global] Notation Qp := cQp.
*)
