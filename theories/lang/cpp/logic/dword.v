(**
 * Copyright (c) 2020 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From iris.algebra Require Import list.
From iris.bi Require Import monpred big_op.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From bedrock.lang Require Import prelude.numbers bi.observe bi.big_op.
From bedrock.lang.cpp.semantics Require Import types genv.
From bedrock.lang.cpp.logic Require Import pred path_pred heap_pred.
From bedrock.lang.cpp Require Import heap_notations.
From bedrock.lang.cpp.semantics Require Import values.

(*TODO: Can these be unified with anything else in cpp2v-core?*)
Section with_Σ.
  Context `{Σ : cpp_logic}.
  #[local] Notation data_at := (forall (pa : paddr) (q : Qp) (n : N), mpred).
  Parameter byte_at : data_at.
  Parameter short_at : data_at.
  Parameter word_at : data_at.
  Parameter dword_at : data_at.
End with_Σ.

Definition page_size : N := 4096.
Definition word_size : N := 64.
Definition page_align (n : N) :=
  N.land n (N.lnot (page_size - 1)%N word_size).

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context (page_mapping : vaddr -> option paddr -> mpred).

  (*This axiom depends on the [page_mapping] predicate exported
    by libnova. The following asserts the axiom for all such
    [page_mapping] predicates (assuming users will apply it
    correctly). It might be better to assert it only for the
    actual [page_mapping]. But I'm not sure how to do that without
    having this file depend on Zeta, or moving this file to Zeta.*)
  Definition data_at_equiv
    (data_at : paddr -> Qp -> N -> mpred) (sz : bitsize) :=
    let ty := Tint sz Unsigned in
    forall (p : ptr) q (n : N),
      p |-> primR ty q (Vint $ Z.of_N n) -|-
        Exists (va : vaddr) (pa : paddr),
          page_mapping (page_align va) (Some (page_align pa)) **
          pinned_ptr va p **
          data_at pa q n.
  Axiom byte_at_equiv : data_at_equiv byte_at W8.
  Axiom short_at_equiv : data_at_equiv short_at W16.
  Axiom word_at_equiv : data_at_equiv word_at W32.
  Axiom dword_at_equiv : data_at_equiv dword_at W64.

  (*TODO: [data_at_borrow] should be provable from [data_at_equiv].*)
  Definition data_at_borrow
    (data_at : paddr -> Qp -> N -> mpred) (sz : bitsize) :=
    let ty := Tint sz Unsigned in
    forall (pa : paddr) q (n : N),
      data_at pa q n
        |-- Forall (va : vaddr),
              page_mapping (page_align va) (Some (page_align pa)) -*
              Forall (p : ptr), pinned_ptr va p -*
                p |-> primR ty q (Vint $ Z.of_N n) **
                page_mapping va (Some pa) **
                Forall n', p |-> primR ty q (Vint $ Z.of_N n') -*
                  data_at pa q n'.
  Axiom byte_at_borrow : data_at_borrow byte_at W8.
  Axiom short_at_borrow : data_at_borrow short_at W16.
  Axiom word_at_borrow : data_at_borrow word_at W32.
  Axiom dword_at_borrow : data_at_borrow dword_at W64.
End with_Σ.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context (data_at : paddr -> Qp -> N -> mpred).

  Definition darrayR_def (sz : bitsize) q (base : paddr) (l : list N) : mpred
    := [∗ list] i ↦ n ∈ l, data_at (base + N.of_nat i * bytesN sz)%N q n.
  Definition darrayR_aux : seal (@darrayR_def). Proof. by eexists. Qed.
  Definition darrayR := darrayR_aux.(unseal).
  Definition darrayR_eq : @darrayR = _ := darrayR_aux.(seal_eq).
End with_Σ.
Arguments darrayR {_ _} _ _ _ _ _%list_scope : assert.
Instance: Params (@darrayR) 5 := {}.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.
  Context {data_at : paddr -> Qp -> N -> mpred} {sz : bitsize}.
  #[local] Notation darrayR := (darrayR data_at sz).

  Lemma darrayR_nil q (base : paddr) :
    darrayR q base nil -|- emp.
  Proof. by rewrite darrayR_eq/darrayR_def big_opL_nil. Qed.

  Lemma darrayR_cons q (l : list N) (base : paddr) (n : N) :
    darrayR q base (n :: l) -|-
            data_at base q n ** darrayR q (base + bytesN sz)%N l.
  Proof.
    rewrite darrayR_eq/darrayR_def big_opL_cons //.
    have ->: (base + N.of_nat 0 * bytesN sz)%N = base by lia.
    set X := ([∗ list] _↦_ ∈ _, data_at (_ + _ * _) _ _)%I.
    set Y := ([∗ list] _↦_ ∈ _, data_at (_ + _ + _ * _) _ _)%I.
    have ->: X -|- Y; last by []. apply: big_sepL_proper => k y H.
    set N := (_ + _ * _)%N; set M := (_ + _ + _ * _)%N.
      by have ->: N = M by lia.
  Qed.

  (*GS: misplaced; what's the right Iris lemma?*)
  Lemma emp_unit_left (P : mpred) : emp ** P -|- P.
  Proof. split'. apply: bi.emp_sep_2. apply: bi.emp_sep_1. Qed.
  Lemma emp_unit_right (P : mpred) : P ** emp -|- P.
  Proof. by rewrite bi.sep_comm emp_unit_left. Qed.
  (*End "misplaced"*)

  Lemma darrayR_app q (l1 l2 : list N) (base : paddr) :
    darrayR q base (l1 ++ l2) -|-
            darrayR q base l1 **
            darrayR q (base + bytesN sz * N.of_nat (List.length l1))%N l2.
  Proof.
    elim: l1 base; [ move => base | move => a l1 IH base ].
    { rewrite app_nil_l nil_length.
      have ->: (base + bytesN sz * N.of_nat 0 = base)%N by lia.
      by rewrite darrayR_nil emp_unit_left. }
    rewrite /= 2!darrayR_cons IH.
    set X := (base + _ + _)%N; set Y := (base + _ * _)%N.
    have ->: X = Y by lia.
      by rewrite bi.sep_assoc.
  Qed.

  Lemma darrayR_cell q (l : list N) (base : paddr) (n : N)
        (i : nat) (H : l !! i = Some n)
    : darrayR q base l -|-
              darrayR q base (take i l) **
              data_at (base + bytesN sz * N.of_nat i) q n **
              darrayR q (base + bytesN sz * (N.of_nat i + 1))%N (drop (S i) l).
  Proof.
    rewrite -(take_drop_middle _ _ _ H) darrayR_app darrayR_cons.
    have L: i < List.length l; first by apply: lookup_lt_is_Some_1; eexists.
    rewrite take_app_le; last by rewrite firstn_length; lia.
    rewrite take_take Nat.min_id firstn_length.
    have ->: i `min` List.length l = i by lia.
    rewrite take_drop_middle //.
    set X := (base + _ * _ + _)%N; set Y := (base + _ * (_ + _))%N.
      by have ->: X = Y by lia.
  Qed.
End with_Σ.
