(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.numbers.
Require Import bedrock.lang.cpp.syntax.types.

Module CV.
  Record t : Set := mk { qual : type_qualifiers ; frac : Qp }.
  Add Printing Constructor t.
  #[global] Bind Scope Qp_scope with t.
  Coercion frac : t >-> Qp.

  Definition add (a b : t) : t :=
    mk (merge_tq a.(qual) b.(qual))(a.(frac) + b.(frac)).

  Lemma eta q : q = mk (qual q) (frac q).
  Proof. by destruct q; intros. Qed.

  Lemma refl cv q_f : mk cv q_f = mk cv q_f.
  Proof. done. Qed.

  (* Notations -- probably actually make these notations? *)
  Definition mut : Qp -> t := mk QM.
  Definition const : Qp -> t := mk QC.
  Definition volatile : Qp -> t := mk QV.
  Definition const_volatile : Qp -> t := mk QCV.

  Notation m := mut.
  Notation c := const.
  Notation v := volatile.
  Notation cv := const_volatile.
  #[deprecated(note="use [CV.cv]")]
  Notation vc := const_volatile (only parsing).
End CV.

#[global] Bind Scope Qp_scope with CV.t.


(* as with C++, we make mutable the default *)
#[global] Coercion CV.mut : Qp >-> CV.t.

Module Type TEST.
  Parameter TEST : CV.t -> CV.t -> CV.t -> CV.t -> Prop.

  (* TODO: to make this work without the [%Qp], we need to register the
     notations for [Qp] as notations in [cvq_scope]. *)
  Goal TEST 1 (CV.c 1) (CV.v 1) (CV.cv 1).
  Abort.

End TEST.
(*
#[global] Notation Qp_plain := stdpp.numbers.Qp.
#[global] Notation Qp := cQp.
*)
