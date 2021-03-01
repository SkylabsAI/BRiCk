(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.proofmode.tactics.
From iris_string_ident Require Import ltac2_string_ident.
From bedrock.lang.prelude Require Import base option.
From bedrock.lang.cpp Require Import ast semantics.values semantics.operator.
From bedrock.lang.cpp.logic Require Import pred operator.

Section with_Σ.
  Context `{has_cpp : cpp_logic} {resolve : genv}.

  (** Can these pointers be validly compared? *)
  (* Written to ease showing [ptr_comparable_symm]. *)
  Definition ptr_comparable p1 p2 res : mpred :=
    (* These premises let you assume that that [p1] and [p2] have an address. *)
    [| is_Some (ptr_vaddr p1) /\ is_Some (ptr_vaddr p2) |] -∗
    ∃ vt1 vt2,
      [| same_address_bool p1 p2 = res |] ∗
      (_valid_ptr vt1 p1 ∗ _valid_ptr vt2 p2) ∗
      ([| same_alloc p1 p2 |] ∨
        ([| p1 = nullptr |] ∨ [| p2 = nullptr |]) ∨
        ([| operator.ptr_unambiguous_cmp vt1 p2 ∧ operator.ptr_unambiguous_cmp vt2 p1 |] ∗
          (live_ptr p1 ∧ live_ptr p2))).

  (* Unlikely to be invertible. *) (* TODO: drop? *)
  Lemma ptr_comparable_eq_comparable p1 p2 res :
    ptr_comparable p1 p2 res ⊢ ptr_eq_comparable p1 p2 res.
  Proof.
    rewrite /ptr_comparable /ptr_eq_comparable.
    iIntros "H" (va1 va2 Hp1 Hp2).
    rewrite (same_address_bool_eq Hp1 Hp2).
    iDestruct ("H" with "[%]") as (vt1 vt2) "($ & (V1 & V2) & D)"; [by eauto|].
    iSplit. 2: { rewrite !_valid_valid. iFrame. }
    iIntros "<-".
    have Addr : same_address p1 p2 by exact: same_address_intro.
    iDestruct "D" as "[%D | [%D | ([%U1 %U2] & L)]]"; [by iIntros "!%" |..]. {
      destruct D as [-> | ->]; first rewrite (comm same_alloc); by iApply same_address_eq_null_1.
    }
    { by iApply (ptr_eq_comparable_unambiguous with "L V1 V2"). }
  Qed.

  Lemma ptr_ord_comparable_comparable p1 p2 res :
    ptr_ord_comparable p1 p2 (λ va1 va2, bool_decide (va1 = va2)) res ⊢ ptr_comparable p1 p2 res.
  Proof.
    iIntros "(? & %Hi & ? & ?)" ([[va1 Hs1] [va2 Hs2]]);
      iExists Relaxed, Relaxed. iFrame.
    by rewrite -(Hi _ _ Hs1 Hs2) (same_address_bool_eq Hs1 Hs2).
  Qed.

  Lemma ptr_comparable_symm p1 p2 res :
    ptr_comparable p1 p2 res ⊢ ptr_comparable p2 p1 res.
  Proof.
    rewrite /ptr_comparable (comm and (is_Some (ptr_vaddr p2))); f_equiv.
    iDestruct 1 as (vt1 vt2) "H"; iExists vt2, vt1.
    (* To ease rearranging conjuncts or changing connectives, we repeat the
    body (which is easy to update), not the nesting structure. *)
    rewrite !(comm and (is_Some (ptr_vaddr p2)), comm same_address_bool p2, comm _ (_valid_ptr vt2 _),
      comm same_alloc p2, comm _ [| p2 = _ |]%I, comm _ (live_ptr p2), comm _ (operator.ptr_unambiguous_cmp vt2 _)).
    iStopProof. repeat f_equiv.
  Qed.

  (* TODO: drop. *)
  Lemma nullptr_ptr_comparable {p res} :
    (is_Some (ptr_vaddr p) -> bool_decide (p = nullptr) = res) ->
    valid_ptr p ⊢ ptr_comparable p nullptr res.
  Proof.
    iIntros "%HresI V" ([Haddr _]); iExists Relaxed, Relaxed.
    iDestruct (same_address_bool_null with "V") as %->.
    iFrame ((HresI Haddr) (eq_refl nullptr)) "V".
    iApply valid_ptr_nullptr.
  Qed.

  (* TODO: drop. *)
  Lemma nullptr_ptr_eq_comparable' {p res} :
    (is_Some (ptr_vaddr p) -> bool_decide (p = nullptr) = res) ->
    valid_ptr p ⊢ ptr_eq_comparable p nullptr res.
  Proof.
    intros HresI. by rewrite nullptr_ptr_comparable // ptr_comparable_eq_comparable.
  Qed.

  (* TODO: drop. *)
  Lemma self_ptr_comparable p :
    valid_ptr p ⊢ ptr_comparable p p true.
  Proof. rewrite -ptr_ord_comparable_comparable. exact: ptr_ord_comparable_self_eq. Qed.

  Lemma ptr_comparable_off_off o1 o2 base p1 p2 res :
    p1 = base .., o1 ->
    p2 = base .., o2 ->
    same_address_bool p1 p2 = res ->
    valid_ptr p1 ∗ valid_ptr p2 ⊢ ptr_comparable p1 p2 res.
  Proof.
    intros ->-> Hs. rewrite -ptr_ord_comparable_comparable.
    apply: ptr_ord_comparable_off_off; [done..|].
    move=> va1 va2 Hs1 Hs2. by rewrite -(same_address_bool_eq Hs1 Hs2).
  Qed.

  (* TODO: drop. *)
  Lemma ptr_comparable_off o1 base p1 res :
    p1 = base .., o1 ->
    same_address_bool p1 base = res ->
    valid_ptr p1 ∗ valid_ptr base ⊢ ptr_comparable p1 base res.
  Proof.
    intros -> Hres. eapply (ptr_comparable_off_off o1 o_id base) => //.
    by rewrite offset_ptr_id.
  Qed.

End with_Σ.
