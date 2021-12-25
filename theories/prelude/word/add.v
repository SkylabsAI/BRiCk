(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *
 * This file is derived from code written (and not distributed) by
 * David Swasey:
 *
 *	Copyright 2017 by David Swasey
 *
 *	SPDX-License-Identifier: LGPL-2.1-or-later
 *
 * Swasey had derived his code from code original to the CompCert
 * verified compiler. That original code is
 *
 *	Copyright by Institut National de Recherche en Informatique et
 *	en Automatique (INRIA) and AbsInt Angewandte Informatik GmbH
 *
 * and used according to the GNU Lesser General Public License v2.1 or
 * later.
 *
 *	SPDX-License-Identifier: LGPL-2.1-or-later
 *
 * Original Code:
 * https://github.com/AbsInt/CompCert/blob/04f499c632a76e460560fc9ec4e14d8216e7fc18/lib/Integers.v
 *
 * Original License:
 * https://github.com/AbsInt/CompCert/blob/04f499c632a76e460560fc9ec4e14d8216e7fc18/LICENSE
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.prelude.word.zlib.
Require Import bedrock.prelude.word.base.
Require Import bedrock.prelude.word.const.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** * Addition for words *)
(** Overview:

- [word.opp], [word.add], [word.sub] with the usual notation in
[word_scope]

- [word.Zopp], [word.Zadd], [word.Zsub] the preceding functions, in
[Z] (these feed [zify])

- [word.opp_cases], [word.add_cases], [word.sub_cases] predicates
specifying the preceding functions

*)

Module word.
  Import base.word const.word.

  Section defs.
    Context {W : wordT}.
    Implicit Types x y : W.

    Definition opp x   : W := of_Z W $ - to_Z x.
    Definition add x y : W := of_Z W $ to_Z x + to_Z y.
    Definition sub x y : W := of_Z W $ to_Z x - to_Z y.
  End defs.

  #[global] Arguments opp : simpl never.
  #[global] Arguments add : simpl never.
  #[global] Arguments sub : simpl never.

  Module Import add_notation.
    Notation "- x" := (opp x) : word_scope.
    Infix "+" := add : word_scope.
    Infix "-" := sub : word_scope.
  End add_notation.

  (**
  Simple tactic for lifting [@eq Z] to [@eq W].

  Note: We cannnot apply functors like Coq's [ZBasicProp] to lift the
  theory for [Z] to a theory for word types because the relations for
  unsigned comparisons we want (namely [x < y := to_Z x < to_Z y] and
  [x ≤ y := to_Z x ≤ to_Z y]) don't satisfy the axiom

    [lt_succ_r x y : x < succ y ↔ x ≤ y]

  assumed by those functors, due to wrap around. In [word 8], for
  example, we have [1 ≤ 255] but [succ 255 = 0 < 1].
  *)
  Tactic Notation "lift_eq" "by" tactic1(tac) :=
    repeat intro; apply of_Z_eq; rewrite !to_of_Z_eqmod; by tac.
  Tactic Notation "lift_eq" uconstr(lem) := lift_eq by rewrite lem.
  Tactic Notation "lift_eq" := lift_eq by idtac.

  (**
  The functions [Zopp], [Zadd], [Zsub] satisfy
  <<
    to_Z (- x) = Zopp modulus (to_Z x)
    to_Z (x + y) = Zadd modulus (to_Z x) (to_Z y)
    to_Z (x - y) = Zsub modulus (to_Z x) (to_Z y)
  >>
  They exist, in part, to feed [zify].
  *)

  Definition Zopp (m z : Z) : Z :=
    if z =? 0 then 0 else m - z.
  Definition Zadd (m z1 z2 : Z) : Z :=
    let s := z1 + z2 in if s <? m then s else s - m.
  Definition Zsub (m z1 z2 : Z) : Z :=
    let d := z1 - z2 in if d <? 0 then d + m else d.

  (**
  The predicates [opp_cases], [add_cases], [sub_cases] specify the
  respective functions using case distinctions [lia] understands.

  They exist, in part, to feed [zify] and are meant to be unfolded.
  *)

  Definition opp_cases (m z z' : Z) : Prop :=
    z = 0 ∧ z' = 0
    ∨ z ≠ 0 ∧ z' = m - z.
  Definition add_cases (m z1 z2 z' : Z) : Prop :=
    let s := z1 + z2 in
    s < m ∧ z' = s
    ∨ m ≤ s ∧ z' = s - m.
  Definition sub_cases (m z1 z2 z' : Z) : Prop :=
    let d := z1 - z2 in
    d < 0 ∧ z' = d + m
    ∨ 0 ≤ d ∧ z' = d.

  Implicit Types W : wordT.

  Section semantics.
    Context {W : wordT}.
    Implicit Types x y : W.

    (** [to_Z (- x)] *)

    Lemma to_Z_opp_Zopp x : to_Z (- x) = Zopp (modulus W) (to_Z x).
    Proof.
      rewrite/opp/Zopp. rewrite to_of_Z_modulo.
      have ? := to_Z_range x. symmetry. case Hb: (_ =? _).
      - apply (Zmod_unique _ _ 0); lia.
      - apply (Zmod_unique _ _ (-1)); lia.
    Qed.

    Lemma Zopp_cases m z : opp_cases m z (Zopp m z).
    Proof. rewrite /opp_cases/Zopp. case Hb: (_ =? _); lia. Qed.

    Lemma to_Z_opp_cases x :
      opp_cases (modulus W) (to_Z x) (to_Z (- x)).
    Proof. rewrite to_Z_opp_Zopp. apply Zopp_cases. Qed.

    Lemma to_Z_opp x :
      to_Z (- x) =
      let u := to_Z x in
      if bool_decide (u = 0) then 0 else modulus W - u.
    Proof.
      destruct (to_Z_opp_cases x) as [[? ->]|[? ->]]; cbn.
      - by rewrite bool_decide_true.
      - by rewrite bool_decide_false.
    Qed.

    (** [to_Z (x + y)] *)

    Lemma to_Z_add_Zadd x y :
      to_Z (x + y) = Zadd (modulus W) (to_Z x) (to_Z y).
    Proof.
      rewrite/add/Zadd. rewrite to_of_Z_modulo.
      move: (to_Z_range x) (to_Z_range y)=>??. symmetry.
      case Hc: (_ <? _).
      - apply (Zmod_unique _ _ 0); lia.
      - apply (Zmod_unique _ _ 1); lia.
    Qed.

    Lemma Zadd_cases m z1 z2 : add_cases m z1 z2 (Zadd m z1 z2).
    Proof. rewrite /add_cases/Zadd. case Hb: (_ <? _); lia. Qed.

    Lemma to_Z_add_cases x y :
      add_cases (modulus W) (to_Z x) (to_Z y) (to_Z (x + y)).
    Proof. rewrite to_Z_add_Zadd. apply Zadd_cases. Qed.

    (* Questionable utility. *)
    Lemma to_Z_add x y :
      to_Z (x + y) =
      let s := to_Z x + to_Z y in
      let m := modulus W in
      if bool_decide (s < m) then s else s - m.
    Proof.
      destruct (to_Z_add_cases x y) as [[? ->]|[? ->]]; cbn.
      - by rewrite bool_decide_true.
      - by rewrite bool_decide_false// Z.nlt_ge.
    Qed.

    (** [to_Z (x - y)] *)

    Lemma to_Z_sub_Zsub x y :
      to_Z (x - y) = Zsub (modulus W) (to_Z x) (to_Z y).
    Proof.
      rewrite/sub/Zsub. rewrite to_of_Z_modulo.
      move: (to_Z_range x) (to_Z_range y)=>??. symmetry.
      case Hb: (_ <? _).
      - apply (Zmod_unique _ _ (-1)); lia.
      - apply (Zmod_unique _ _ 0); lia.
    Qed.

    Lemma Zsub_cases m z1 z2 : sub_cases m z1 z2 (Zsub m z1 z2).
    Proof. rewrite /sub_cases/Zsub. case Hb: (_ <? _); lia. Qed.

    Lemma to_Z_sub_cases x y :
      sub_cases (modulus W) (to_Z x) (to_Z y) (to_Z (x - y)).
    Proof. rewrite to_Z_sub_Zsub. apply Zsub_cases. Qed.

    (* Questionable utility. *)
    Lemma to_Z_sub x y :
      to_Z (x - y) =
      let d := to_Z x - to_Z y in
      if bool_decide (d < 0) then d + modulus W else d.
    Proof.
      destruct (to_Z_sub_cases x y) as [[? ->]|[? ->]]; cbn.
      - by rewrite bool_decide_true//.
      - by rewrite bool_decide_false// Z.nlt_ge.
    Qed.

  End semantics.

  #[local] Open Scope word_scope.

  (** [opp] *)

  Lemma of_Z_opp W z : of_Z W (- z) = - of_Z W z.
  Proof. lift_eq. Qed.

  Lemma opp_0 W : - 0@{W} = 0.
  Proof. lift_eq. Qed.

  Lemma opp_1 W : - 1@{W} = (-1).
  Proof. lift_eq. Qed.

  Lemma opp_m1 W : - (-1)@{W} = 1.
  Proof. lift_eq. Qed.

  Section opp.
    Context {W : wordT}.
    Implicit Types x y : W.

    Lemma opp_to_Z x : - x = of_Z W (- to_Z x).
    Proof. done. Qed.

    Lemma opp_signed x : - x = of_Z W (- signed x).
    Proof. apply of_Z_eq. by rewrite signed_to_Z. Qed.

    Lemma opp_involutive x : - - x = x.
    Proof. lift_eq Z.opp_involutive. Qed.

    #[global] Instance opp_inj : Inj (=@{W}) (=) opp.
    Proof. move=>x1 x2 /(f_equal opp). by rewrite !opp_involutive. Qed.

    Lemma opp_inj_wd x y : - x = - y ↔ x = y.
    Proof. split. exact: opp_inj. by intros->. Qed.

    Lemma eq_opp_l x y : - x = y ↔ x = - y.
    Proof. by rewrite -(opp_inj_wd (- x) y) opp_involutive. Qed.

    Lemma eq_opp_r x y : x = - y ↔ - x = y.
    Proof. symmetry. apply eq_opp_l. Qed.

  End opp.
  #[global] Hint Opaque opp : typeclass_instances.

  (** [add], [sub] *)

  Section add.
    Context {W : wordT}.
    Implicit Types x y : W.

    Lemma add_to_Z x y : x + y = of_Z W (to_Z x + to_Z y).
    Proof. done. Qed.

    Lemma add_signed x y : x + y = of_Z W (signed x + signed y).
    Proof. by rewrite add_to_Z !signed_to_Z. Qed.

    Lemma sub_to_Z x y : x - y = of_Z W (to_Z x - to_Z y).
    Proof. done. Qed.

    Lemma sub_signed x y : x - y = of_Z W (signed x - signed y).
    Proof. apply of_Z_eq. by rewrite !signed_to_Z. Qed.

    (** Lots of properties inherited from [Z] *)

    #[global] Instance add_comm : Comm (=) (add (W:=W)).
    Proof. lift_eq Z.add_comm. Qed.

    #[global] Instance add_assoc : Assoc (=) (add (W:=W)).
    Proof. lift_eq Z.add_assoc. Qed.

    Lemma add_sub_assoc x y z : x + (y - z) = (x + y) - z.
    Proof. lift_eq Z.add_sub_assoc. Qed.

    #[global] Instance add_0_r : RightId (=) 0@{W} add.
    Proof. lift_eq Z.add_0_r. Qed.

    #[global] Instance add_0_l : LeftId (=) 0@{W} add.
    Proof. lift_eq Z.add_0_l. Qed.

    #[global] Instance sub_0_r : RightId (=) 0 (@sub W).
    Proof. lift_eq Z.sub_0_r. Qed.

    Lemma sub_0_l x : 0 - x = - x.
    Proof. lift_eq Z.sub_0_l. Qed.

    Lemma sub_diag x : x - x = 0.
    Proof. lift_eq Z.sub_diag. Qed.

    Lemma sub_add x y : y - x + x = y.
    Proof. lift_eq Z.sub_add. Qed.

    Lemma sub_add_distr x y z : x - (y + z) = (x - y) - z.
    Proof. lift_eq Z.sub_add_distr. Qed.

    Lemma sub_sub_distr x y z : x - (y - z) = (x - y) + z.
    Proof. lift_eq Z.sub_sub_distr. Qed.

    Lemma add_sub_swap x y z : x + y - z = x - z + y.
    Proof. lift_eq Z.add_sub_swap. Qed.

    Lemma add_opp_l x y : - x + y = y - x.
    Proof. lift_eq Z.add_opp_l. Qed.

    Lemma add_opp_r x y : x + - y = x - y.
    Proof. lift_eq Z.add_opp_r. Qed.

    Lemma sub_opp_l x y : - x - y = - y - x.
    Proof. lift_eq Z.sub_opp_l. Qed.

    Lemma sub_opp_r x y : x - - y = x + y.
    Proof. lift_eq Z.sub_opp_r. Qed.

    Lemma add_opp_diag_l x : - x + x = 0.
    Proof. lift_eq Z.add_opp_diag_l. Qed.

    Lemma add_opp_diag_r x : x + - x = 0.
    Proof. lift_eq Z.add_opp_diag_r. Qed.

    Lemma opp_add_distr x y : - (x + y) = - x + - y.
    Proof. lift_eq Z.opp_add_distr. Qed.

    Lemma opp_sub_distr x y : - (x - y) = - x + y.
    Proof. lift_eq Z.opp_sub_distr. Qed.

    Lemma add_cancel_l x y c : c + x = c + y ↔ x = y.
    Proof.
      split=>[EQ|->//]. apply to_Z_inj_eqmod.
      apply (f_equal to_Z) in EQ. move: EQ.
      rewrite !to_of_Z_modulo !Z.mod_eq//.
      move: (_ `div` _) (_ `div` _)=>a b. exists (b - a)%Z. lia.
    Qed.

    Lemma add_cancel_r x y c : x + c = y + c ↔ x = y.
    Proof. rewrite [x+c]comm_L [y+c]comm_L. apply add_cancel_l. Qed.

    Lemma sub_cancel_l x y z : x - y = x - z ↔ y = z.
    Proof.
      rewrite -(add_cancel_l (x - y) (x - z) (- x)).
      rewrite !add_sub_assoc add_opp_diag_l !sub_0_l. by rewrite opp_inj_wd.
    Qed.

    Lemma sub_cancel_r x y z : x - z = y - z ↔ x = y.
    Proof.
      stepl (x - z + z = y - z + z) by apply add_cancel_r.
      by rewrite -!sub_sub_distr sub_diag !right_id_L.
    Qed.

    Lemma add_move_l x y z : x + y = z ↔ y = z - x.
    Proof.
      stepl (x + y - x = z - x) by apply sub_cancel_r.
      by rewrite add_comm -add_sub_assoc sub_diag right_id_L.
    Qed.

    Lemma add_move_r x y z : x + y = z ↔ x = z - y.
    Proof. by rewrite add_comm add_move_l. Qed.

    Lemma sub_move_l x y z : x - y = z ↔ - y = z - x.
    Proof. by rewrite -(add_opp_r x y) add_move_l. Qed.

    Lemma sub_move_r x y z : x - y = z ↔ x = z + y.
    Proof. by rewrite -(add_opp_r x y) add_move_r sub_opp_r. Qed.

    Lemma add_move_0_l x y : x + y = 0 ↔ y = - x.
    Proof. by rewrite add_move_l sub_0_l. Qed.

    Lemma add_move_0_r x y : x + y = 0 ↔ x = - y.
    Proof. by rewrite add_move_r sub_0_l. Qed.

    Lemma sub_move_0_l x y : x - y = 0 ↔ - y = - x.
    Proof. by rewrite sub_move_l sub_0_l. Qed.

    Lemma sub_move_0_r x y : x - y = 0 ↔ x = y.
    Proof. by rewrite sub_move_r add_0_l. Qed.

    Lemma add_simpl_l x y : x + y - x = y.
    Proof. lift_eq Z.add_simpl_l. Qed.

    Lemma add_simpl_r x y : x + y - y = x.
    Proof. lift_eq Z.add_simpl_r. Qed.

    Lemma sub_simpl_l x y : - x - y + x = - y.
    Proof. lift_eq Z.sub_simpl_l. Qed.

    Lemma sub_simpl_r x y : x - y + y = x.
    Proof. lift_eq Z.sub_simpl_r. Qed.

    Lemma add_add_simpl_l_l x y z : (x + y) - (x + z) = y - z.
    Proof. lift_eq Z.add_add_simpl_l_l. Qed.

    Lemma add_add_simpl_l_r x y z : (x + y) - (z + x) = y - z.
    Proof. lift_eq Z.add_add_simpl_l_r. Qed.

    Lemma add_add_simpl_r_l x y z : (x + y) - (y + z) = x - z.
    Proof. lift_eq Z.add_add_simpl_r_l. Qed.

    Lemma add_add_simpl_r_r x y z : (x + y) - (z + y) = x - z.
    Proof. lift_eq Z.add_add_simpl_r_r. Qed.

    Lemma sub_add_simpl_r_l x y z : (x - y) + (y + z) = x + z.
    Proof. lift_eq Z.sub_add_simpl_r_l. Qed.

    Lemma sub_add_simpl_r_r x y z : (x - y) + (z + y) = x + z.
    Proof. lift_eq Z.sub_add_simpl_r_r. Qed.

    Lemma add_shuffle0 x y p : x + y + p = x + p + y.
    Proof. lift_eq Z.add_shuffle0. Qed.

    Lemma add_shuffle1 x y p q : (x + y) + (p + q) = (x + p) + (y + q).
    Proof. lift_eq Z.add_shuffle1. Qed.

    Lemma add_shuffle2 x y p q : (x + y) + (p + q) = (x + q) + (y + p).
    Proof. lift_eq Z.add_shuffle2. Qed.

    Lemma add_shuffle3 x y z : x + (y + z) = y + (x + z).
    Proof. lift_eq Z.add_shuffle3. Qed.

  End add.
  #[global] Hint Opaque add sub : typeclass_instances.

End word.
Export word.add_notation.
