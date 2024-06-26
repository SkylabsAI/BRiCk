(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export stdpp.gmap.
Require Export stdpp.mapset.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.fin_sets.
Require Import bedrock.prelude.list_numbers.

(* To upstream to Iris: using [mapseq_eq] directly would unfold a TC opaque
definition and interfere with TC search. *)
Lemma gset_eq `{Countable A} (X1 X2 : gset A) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof. apply mapset_eq. Qed.

(** [set_map] specialized to [gset]; avoids awkward type annotations such as
[set_map (C := gset _) (D := gset _)].
*)
#[global] Notation gset_map := (set_map (C := gset _) (D := gset _)) (only parsing).

#[global] Notation gset_concat_map :=
  (set_concat_map (C := gset _) (D := gset _)) (only parsing).

(* Like [set_concat_map], but purely in terms of gsets.
*)
Section gset_bind.
  Context `{Countable A} `{Countable B}.

  Definition gset_bind (f : A → gset B) (xs : gset A) : gset B :=
    gset_concat_map (elements ∘ f) xs.

  Lemma gset_bind_empty f :
    gset_bind f ∅ = ∅.
  Proof. done. Qed.

  Lemma elem_of_gset_bind f b xs :
    b ∈ gset_bind f xs ↔ ∃ x, x ∈ xs ∧ b ∈ f x.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_gset_bind f b xs P Q :
    (∀ x, SetUnfoldElemOf x xs (P x)) → (∀ x, SetUnfoldElemOf b (f x) (Q x)) →
    SetUnfoldElemOf b (gset_bind f xs) (∃ x, P x ∧ Q x).
  Proof. constructor. rewrite elem_of_gset_bind. set_solver. Qed.

  Lemma gset_bind_union f xs1 xs2 :
    gset_bind f (xs1 ∪ xs2) =
    gset_bind f xs1 ∪ gset_bind f xs2.
  Proof. set_solver. Qed.

  Lemma gset_bind_singleton f a :
    gset_bind f {[ a ]} = f a.
  Proof. set_solver. Qed.
End gset_bind.

Section lookup_insert.

  Lemma lookup_insert_iff `{Countable K, A} (m : gmap K A) k k' a :
    <[ k := a ]> m !! k' = if bool_decide (k = k') then Some a else m !! k'.
  Proof. by case: bool_decide_reflect => [<-|?]; rewrite (lookup_insert, lookup_insert_ne). Qed.

End lookup_insert.

Section set_seqZ.
  #[local] Open Scope Z_scope.

  Definition set_seqZ `{!Singleton Z C, !Union C, !Empty C} (i j : Z) : C :=
    list_to_set (seqZ i j).

  Section dom_seqZ.
    Context  `{!∀ A, Dom (M A) D, !FMap M,
                 HL : !∀ A, Lookup Z A (M A),
                 HE : !∀ A, Empty (M A),
                 HP : !∀ A, PartialAlter Z A (M A)}.
    Context `{!OMap M, !Merge M, HF : !∀ A, MapFold Z A (M A), !ElemOf Z D, !Empty D,
              !Singleton Z D, !Union D, !Intersection D, !Difference D, !FinMapDom Z M D}.

    Lemma dom_seqZ {A} (start : Z) (xs : list A) :
      dom (map_seqZ start xs : M A) ≡ (set_seqZ start (start + lengthZ xs) : D).
    Proof using FinMapDom0.
      rewrite /set_seqZ.
      elim: xs start => [|x xs IH] start.
      - rewrite lengthN_nil /= Z.add_0_r seqZ_eq_nil' //; apply dom_empty.
      - have ? : (start < start + (lengthN xs + 1)%N) by lia.
        rewrite [X in dom X] /= dom_insert lengthN_cons seqZ_eq_cons //.
        rewrite N.add_1_r N2Z.inj_succ -Z.add_succ_comm Z.add_1_r.
        by rewrite /= -IH.
    Qed.

    Lemma dom_seqZ_L `{!LeibnizEquiv D, A} (start : Z) (xs : list A) :
      dom (map_seqZ start xs : M A) = (set_seqZ start (start + lengthN xs) : D).
    Proof using FinMapDom0.
      apply leibniz_equiv, dom_seqZ.
    Qed.

    Lemma elem_of_set_seqZ x i j : x ∈ (set_seqZ i j : D) <-> (i ≤ x < j).
    Proof using FinMapDom0.
      by rewrite /set_seqZ elem_of_list_to_set elem_of_seqZ.
    Qed.

    Lemma size_set_seqZ `{!Elements Z D, !FinSet Z D} i j : size (set_seqZ i j : D) = Z.to_nat (j - i).
    Proof using FinMapDom0.
      have ? := NoDup_seqZ i j.
      by rewrite /set_seqZ size_list_to_set // -(inj_iff N.of_nat) [N.of_nat _]lengthN_seqZ Z_nat_N.
    Qed.

  End dom_seqZ.

End set_seqZ.
