(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.

#[local] Open Scope Z_scope.

(* see
 * https://gcc.gnu.org/onlinedocs/gcc/Other-Builtins.html
 *)

Module Import churn_bits.
  (* TODO: using bool_decide would simplify this reasoning. *)
  Ltac churn_bits' :=
    repeat match goal with
    | |- context[(?l <=? ?r)%Z] =>
      let Hnb := fresh "Hnb" in
      let Hn := fresh "Hn" in
      destruct (l <=? r)%Z eqn:Hnb;
        set (Hn := Hnb);
        [ apply Z.leb_le in Hn
        | apply Z.leb_gt in Hn]
    | |- context[(?l <? ?r)%Z] =>
      let Hnb := fresh "Hnb" in
      let Hn := fresh "Hn" in
      destruct (l <? r)%Z eqn:Hnb;
        set (Hn := Hnb);
        [ apply Z.ltb_lt in Hn
        | apply Z.ltb_ge in Hn]
    end; rewrite ?andb_false_l ?andb_false_r ?andb_true_l ?andb_true_r
                ?orb_false_l ?orb_false_r ?orb_true_l ?orb_true_r ?Z.bits_0 //=;
                try lia.

  Ltac churn_bits :=
    apply Z.bits_inj'=> n ?;
    repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia);
    rewrite !Z.testbit_ones; try lia;
    churn_bits'.
End churn_bits.

Section Byte.
  Definition _get_byte (x: Z) (n: nat): Z := Z.land (x ≫ (8 * n)) (Z.ones 8).
  Definition _set_byte (x: Z) (n: nat): Z := (Z.land (Z.ones 8) x) ≪ (8 * n).

  Section Theory.
    Lemma _get_byte_0:
      forall (idx: nat),
        _get_byte 0 idx = 0.
    Proof. intros; by rewrite /_get_byte Z.shiftr_0_l Z.land_0_l. Qed.

    Lemma _set_byte_0:
      forall (idx: nat),
        _set_byte 0 idx = 0.
    Proof. intros; by rewrite /_set_byte Z.shiftl_0_l. Qed.

    #[local] Lemma Z_mul_of_nat_S (z : Z) (n : nat) : (z * S n)%Z = (z + z * n)%Z.
    Proof. lia. Qed.

    Lemma _get_byte_S_idx:
      forall (v: Z) (idx: nat),
        _get_byte v (S idx) = _get_byte (v ≫ 8) idx.
    Proof.
      intros; rewrite /_get_byte.
      by rewrite Z.shiftr_shiftr ?Z_mul_of_nat_S; lia.
    Qed.

    Lemma _get_byte_lor:
      forall (v v': Z) (idx: nat),
        _get_byte (Z.lor v v') idx =
        Z.lor (_get_byte v idx) (_get_byte v' idx).
    Proof. intros *; rewrite /_get_byte; churn_bits. Qed.

    Lemma _set_byte_S_idx:
      forall (v: Z) (idx: nat),
        _set_byte v (S idx) = ((_set_byte v idx) ≪ 8)%Z.
    Proof.
      intros; rewrite /_set_byte.
      by rewrite Z.shiftl_shiftl ?Z_mul_of_nat_S ?(Z.add_comm 8); lia.
    Qed.

    Lemma _set_byte_lor:
      forall (v v': Z) (idx: nat),
        _set_byte (Z.lor v v') idx =
        Z.lor (_set_byte v idx) (_set_byte v' idx).
    Proof. intros *; rewrite /_set_byte; churn_bits. Qed.

    Lemma _set_byte_shiftl_idx:
      forall (idx idx': nat) shift v,
        idx' <= idx ->
        (shift = 8 * Z.of_nat idx')%Z ->
        (_set_byte v idx ≫ shift)%Z = _set_byte v (idx - idx').
    Proof.
      intros * Hidx Hshift; rewrite /_set_byte; subst; churn_bits.
      f_equal; lia.
    Qed.

    Lemma _get_byte_bound:
      forall (v : Z) (idx : nat),
        (0 <= _get_byte v idx < 256)%Z.
    Proof.
      intros *; rewrite /_get_byte Z.land_ones; try lia.
      pose proof (Z.mod_pos_bound (v ≫ (8 * idx)) 256) as [? ?]; try lia.
      now replace (2 ^ 8) with 256%Z by lia.
    Qed.

    Lemma _get_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _get_byte v idx)%Z.
    Proof. intros *; pose proof (_get_byte_bound v idx); lia. Qed.

    Lemma _set_byte_bound:
      forall (v : Z) (idx : nat),
        (0 <= _set_byte v idx < 2 ^ (8 * (idx + 1)))%Z.
    Proof.
      intros; rewrite /_set_byte Z.land_comm Z.land_ones; try lia.
      rewrite Z.shiftl_mul_pow2; try lia.
      pose proof (Z.mod_pos_bound v 256) as [? ?]; try lia.
      replace (2 ^ (8 * (idx + 1))) with ((2 ^ 8) * (2 ^ (8 * idx)))
        by (rewrite Z.mul_add_distr_l Zpower_exp; lia).
      replace (2 ^ 8) with 256%Z by lia.
      split.
      - apply Z.mul_nonneg_nonneg; auto.
        apply Z.pow_nonneg; lia.
      - apply Zmult_lt_compat_r; auto.
        apply Z.pow_pos_nonneg; lia.
    Qed.

    Lemma _set_byte_nonneg:
      forall (v: Z) (idx: nat),
        (0 <= _set_byte v idx)%Z.
    Proof. intros *; pose proof (_set_byte_bound v idx); lia. Qed.

    Lemma _set_byte_testbit_low:
      forall idx v n,
        0 <= n ->
        n < 8 * Z.of_nat idx ->
        Z.testbit (_set_byte v idx) n = false.
    Proof.
      intros * Hnonneg Hn.
      repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
      rewrite !Z.testbit_ones; lia.
    Qed.

    Lemma _set_byte_testbit_high:
      forall idx' idx v n,
        (idx' < idx)%nat ->
        8 * Z.of_nat idx <= n ->
        Z.testbit (_set_byte v idx') n = false.
    Proof.
      intros * Hidx Hn.
      repeat (rewrite ?Z.lor_spec ?Z.shiftl_spec ?Z.land_spec ?Z.shiftr_spec; try lia).
      rewrite !Z.testbit_ones; lia.
    Qed.

    Lemma _set_byte_land_no_overlap:
      forall (idx idx': nat) mask v,
        idx <> idx' ->
        (mask = Z.ones 8 ≪ (8 * Z.of_nat idx'))%Z ->
        Z.land (_set_byte v idx) mask = 0.
    Proof. intros * Hidx Hmask; rewrite /_set_byte; subst; churn_bits. Qed.

    Lemma _set_byte_land_useless:
      forall idx mask v,
        (mask = Z.ones 8 ≪ (8 * Z.of_nat idx))%Z ->
        Z.land (_set_byte v idx) mask =
        _set_byte v idx.
    Proof. intros * Hmask; rewrite /_set_byte; subst; churn_bits. Qed.

    Lemma _set_byte_shiftr_big:
      forall (idx: nat) (idx': Z) v,
        (Z.of_nat idx < idx')%Z ->
        (_set_byte v idx ≫ (8 * idx'))%Z = 0.
    Proof. intros * Hidx; rewrite /_set_byte; churn_bits. Qed.

    Lemma _get_0_set_0_eq:
      forall v,
        _get_byte v 0 = _set_byte v 0.
    Proof. intros *; rewrite /_get_byte/_set_byte; churn_bits. Qed.

    Lemma _set_get_0:
      forall v idx,
        _set_byte (_get_byte v 0) idx = _set_byte v idx.
    Proof.
      intros *; rewrite /_get_byte/_set_byte.
      apply Z.bits_inj'=> n ?.
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      repeat (rewrite ?Z.shiftl_spec; try lia).
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      assert (n < 8 * idx \/ 8 * idx <= n) as [Hn | Hn] by lia.
      - rewrite !Z.testbit_neg_r; [reflexivity | lia.. ].
      - rewrite !Z.shiftr_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
        churn_bits'.
    Qed.

    Lemma _get_set_byte_no_overlap:
      forall (v: Z) (idx idx': nat),
        idx <> idx' ->
        _get_byte (_set_byte v idx) idx' = 0.
    Proof. intros * Hidx; rewrite /_get_byte/_set_byte; churn_bits. Qed.

    Lemma _get_set_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _get_byte (_set_byte v idx) idx = _get_byte v 0.
    Proof.
      intros *; rewrite /_get_byte/_set_byte; churn_bits.
      f_equal; lia.
    Qed.

    Lemma _set_get_byte_roundtrip:
      forall (v: Z) (idx: nat),
        _set_byte (_get_byte v idx) idx =
        _get_byte v idx ≪ (8 * idx).
    Proof.
      intros *; rewrite /_get_byte/_set_byte.

      apply Z.bits_inj' => n ?.
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      repeat (rewrite ?Z.shiftl_spec; try lia).
      repeat (rewrite ?Z.lor_spec ?Z.land_spec; try lia).
      assert (n < 8 * idx \/ 8 * idx <= n) as [Hn | Hn] by lia.
      - rewrite !Z.testbit_neg_r; [reflexivity | lia.. ].
      - rewrite !Z.shiftr_spec; try lia.
        rewrite !Z.testbit_ones; try lia.
        churn_bits'.
    Qed.
  End Theory.
End Byte.
