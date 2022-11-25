(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.numbers.


Declare Scope cQp_scope.
Delimit Scope cQp_scope with cQp.

Record cQp : Set := mk { is_const : bool ; frac : Qp }. 
Add Printing Constructor cQp.
Bind Scope cQp_scope with cQp.
(* Coercion frac : cQp >-> Qp. *)
  
Module cQp.
  
  Definition of_Qp : Qp -> cQp := mk false.
  (* Coercion to [Qp] *)
  
  Definition add (a b : cQp) : cQp :=
    match a, b with
    | mk false q_a, mk false q_b => mk false (q_a + q_b)
    | mk _ q_a, mk _ q_b => mk true (q_a + q_b)
    end.

  Lemma eta q : q = mk (is_const q) (frac q).
  Proof. by destruct q; intros. Qed.

  Lemma refl q_c q_f : mk q_c q_f = mk q_c q_f.
  Proof. done. Qed.
  
  Module Import notations.

    Notation "1" := (mk false (pos_to_Qp 1)) : cQp_scope.
    Infix "+" := add : cQp_scope.

  End notations.
  
End cQp.

(* TODO: which Qp's to fix into cQp and which we leave? *)
#[global] Coercion cQp.of_Qp : Qp >-> cQp.
  
Export cQp.notations.

(* 
#[global] Notation Qp_plain := stdpp.numbers.Qp.
#[global] Notation Qp := cQp.
*)
