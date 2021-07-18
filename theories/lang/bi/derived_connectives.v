(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From iris.bi Require Import bi.

Definition default_false {PROP : bi} {A} (P : A -> PROP) (oa : option A) : PROP :=
  default False%I (P <$> oa).
Arguments default_false {_ _} _ !_ /.

Section default_false.
  Context {PROP : bi} `{P : A -> PROP} (oa : option A).

  Lemma default_false_prop (P_PROP : PROP -> Type) :
    P_PROP False%I ->
    (∀ a : A, P_PROP (P a)) ->
    P_PROP (default_false P oa).
  Proof. by case: oa => /=. Qed.

  #[global] Instance default_false_prop_persistent : (∀ a : A, Persistent (P a)) -> Persistent (default_false P oa).
  Proof. apply: default_false_prop. Qed.
  #[global] Instance default_false_prop_affine : (∀ a : A, Affine (P a)) -> Affine (default_false P oa).
  Proof. apply: default_false_prop. Qed.
  #[global] Instance default_false_timeless : (∀ a : A, Timeless (P a)) -> Timeless (default_false P oa).
  Proof. apply: default_false_prop. Qed.
End default_false.
