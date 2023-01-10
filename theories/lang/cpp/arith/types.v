(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base bedrock.prelude.numbers.
Require Export bedrock.lang.prelude.platform.

#[local] Open Scope Z_scope.

(** ** Signed and Unsigned *)
Variant signed : Set := Signed | Unsigned.
#[global] Instance signed_eq_dec: EqDecision signed.
Proof. solve_decision. Defined.
#[global] Instance signed_countable : Countable signed.
Proof.
  apply (inj_countable'
    (λ s, if s is Signed then true else false)
    (λ b, if b then Signed else Unsigned)).
  abstract (by intros []).
Defined.

(** ** Integral Types *)

Lemma of_size_gt_O w : (0 < 2 ^ bitsN w)%Z.
Proof. destruct w; reflexivity. Qed.
(* Hint Resolve of_size_gt_O. *)

Definition max_val (bits : bitsize) (sgn : signed) : Z :=
  match sgn with
  | Signed => 2 ^ (bitsN bits - 1) - 1
  | Unsigned => 2 ^ (bitsN bits) - 1
  end%N.

Definition min_val (bits : bitsize) (sgn : signed) : Z :=
  match sgn with
  | Unsigned => 0
  | Signed => - (2 ^ (bitsN bits - 1))
  end.

Definition bound (bits : bitsize) (sgn : signed) (v : Z) : Prop :=
  min_val bits sgn <= v <= max_val bits sgn.
