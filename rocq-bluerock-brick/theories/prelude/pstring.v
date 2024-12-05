(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Strings.PString.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.
Require Import stdpp.numbers.
Require Import stdpp.relations.

Export PrimString.PStringNotations.

#[global,program]
Instance eqdec_char63 : EqDecision char63 := fun c1 c2 =>
  match PrimInt63.eqb c1 c2 as c return PrimInt63.eqb c1 c2 = c -> _ with
  | true => _
  | false => _
  end eq_refl.
Next Obligation.
  intros c1 c2 Hcmp. left. apply Uint63.eqb_correct. exact Hcmp.
Qed.
Next Obligation.
  intros c1 c2 Hcmp. right. intros H. rewrite H in Hcmp.
  rewrite Uint63.eqb_refl in Hcmp. inversion Hcmp.
Qed.

#[global, program]
Instance eqdec_pstring : EqDecision string := fun i1 i2 =>
  match PrimString.compare i1 i2 as c return PrimString.compare i1 i2 = c -> _ with
  | Eq => _
  | _  => _
  end eq_refl.
Next Obligation.
  left. apply compare_eq_correct. assumption.
Qed.
Next Obligation.
  intros ? ? Hcmp. right. intros H.
  rewrite H, compare_refl in Hcmp. inversion Hcmp.
Qed.
Next Obligation.
  intros ? ? Hcmp. right. intros H.
  rewrite H, compare_refl in Hcmp. inversion Hcmp.
Qed.

#[global] Instance string_inhabited : Inhabited string.
Proof. constructor. exact ""%pstring. Defined.

(* Module strongly inspired from [stdpp.pretty]. *)
Module N.
  #[local] Open Scope N_scope.

  Definition to_string_digit (n : N) : string :=
    match n with
    | 0 => "0"%pstring
    | 1 => "1"%pstring
    | 2 => "2"%pstring
    | 3 => "3"%pstring
    | 4 => "4"%pstring
    | 5 => "5"%pstring
    | 6 => "6"%pstring
    | 7 => "7"%pstring
    | 8 => "8"%pstring
    | _ => "9"%pstring
    end.

  Fixpoint to_string_aux (n : N) (acc : Acc (<)%N n) (s : string) : string :=
    match decide (0 < n) with
    | left H =>
        to_string_aux (n `div` 10)
          (Acc_inv acc (N.div_lt n 10 H eq_refl))
          (cat (to_string_digit (n `mod` 10)) s)
    | right _ => s
    end.

  Definition to_string (n : N) : string :=
    match n with
    | N0 => "0"%pstring
    | _  => to_string_aux n (wf_guard (S (N.size_nat n)) N.lt_wf_0 n) ""%pstring
    end.
End N.
