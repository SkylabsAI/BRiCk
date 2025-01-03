(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.lang.cpp.syntax.core.

#[local] Fixpoint size {lang} (n : name' lang) : nat :=
  match n with
  | Ninst n ls => S (size n)
  | Nglobal _ => 1
  | Nscoped n _ => S (size n)
  | Nunsupported _ => 1
  | Ndependent _ => 1
  end.

Lemma by_size {lang} (n1 n2 : name' lang) : n1 = n2 -> size n1 = size n2.
Proof. intros; subst. eauto. Qed.
