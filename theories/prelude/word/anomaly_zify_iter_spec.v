(*
 * Copyright (C) BedRock Systems Inc. 2022
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

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(**
We repeat much of ./base.v, ./type.v, ./constants.v, ./add.v using Coq
modules rather than canonical strucutures.

This serves two purposes:

(A) It enables experiments with [zify] and [lia] that are presently
blocked for word types based on canonical structures. Specifically, it
satisfies [zify]'s restriction to syntactic type equality. (Due to
this restriction, [zify] does not recognize, e.g., [word 8 =
word.word_car (word_S 7)] and so does not let us register operations
on word types based on canonical structures.)

(B) It enables concrete comparisons between the two approaches wrt
multi-wordsize operations.

The experiements in (A)

- demonstrate that [lia] can be made to solve goals for word types

- show us how [zify] is intended to massage goals for consumption by
[lia], meaning we can likely define a (slower) work-alike in Ltac2 for
use while we wait for [zify] to improve

- uncovered an anomaly in [zify_iter_specs]

*)

Declare Scope word_scope.
Delimit Scope word_scope with W.

Module Type WORD_SIZE.

  Parameter Inline bitsize : nat.

  Axiom bitsize_nonzero : bitsize ≠ 0%nat.

End WORD_SIZE.

Module Type WORD_TYPE (Import WS : WORD_SIZE).

  Parameter t : Set.
  #[global] Bind Scope word_scope with t.

  Parameter unsigned : t → Z.
  Parameter repr : Z → t.

  Axiom unsigned_range' : ∀ x, 0 ≤ unsigned x < 2 ^ bitsize.
  Axiom unsigned_repr_modulo' : ∀ z, unsigned (repr z) = z `mod` 2 ^ bitsize.
  Axiom repr_unsigned : ∀ x, repr (unsigned x) = x.

End WORD_TYPE.

(**
The lack of a [WORD_TYPE WS] ascription matters for goals like
[(-0x1)%i8 = 0xFF%u8].
*)
Module WordType (Import WS : WORD_SIZE).

  Record _t : Set := Word {
    word_val : Z;
    word_range : -1 < word_val < 2 ^ bitsize;
  }.
  #[global] Arguments Word {_} _ : assert.

  Lemma Word_eq {z1 z2} p1 p2 : z1 = z2 → @Word z1 p1 = @Word z2 p2.
  Proof. intros ->. f_equal. apply proof_irrel. Qed.

  #[global] Hint Extern 0 (_ =@{_t}  _) =>
    simple apply @Word_eq; solve [trivial] : core.

  Module Import type_notation.
    Add Printing Constructor _t.
  End type_notation.

  Lemma pf z : -1 < Z.mod_pow2 bitsize z < 2 ^ bitsize.
  Proof. have := Z.mod_pow2_range bitsize z. lia. Qed.

  Definition t : Set := _t.

  #[global] Hint Extern 0 (_ =@{t}  _) =>
    simple apply @Word_eq; solve [trivial] : core.

  Definition unsigned (x : t) : Z := word_val x.

  Definition repr (z : Z) : t := Word (pf z).

  Lemma unsigned_range' x : 0 ≤ unsigned x < 2 ^ bitsize.
  Proof. destruct x. cbn. lia. Qed.

  Lemma unsigned_repr_modulo' z : unsigned (repr z) = z `mod` 2 ^ bitsize.
  Proof. cbn. apply Z.mod_pow2_spec. Qed.

  Lemma repr_unsigned x : repr (unsigned x) = x.
  Proof.
    destruct x as [x ?]. cbn. apply Word_eq.
    rewrite Z.mod_pow2_spec. apply Z.mod_small. lia.
  Qed.

End WordType.

Module Type WORD_BASE
  (Import WS : WORD_SIZE)
  (Import WT : WORD_TYPE WS).

  (** [bitsize] *)

  Class BitsizeAtLeast (n : nat) : Prop :=
    bitsize_at_least : (n ≤ bitsize)%nat.
  #[global] Hint Mode BitsizeAtLeast + : typeclass_instances.
  #[global] Arguments bitsize_at_least _ {_} : assert.

  #[global] Hint Resolve bitsize_nonzero : core.

  Lemma bitsize_min : 1 ≤ bitsize.
  Proof. have := bitsize_nonzero. lia. Qed.
  #[global] Hint Resolve bitsize_min : core.

  Lemma bitsize_pos : 0 < bitsize.
  Proof. have := bitsize_min. lia. Qed.
  #[global] Hint Resolve bitsize_pos : core.

  (** [modulus] *)

  Definition modulus : Z := two_power_nat bitsize.
  #[global] Arguments modulus : simpl never.

  Lemma modulus_bitsize : modulus = 2 ^ bitsize.
  Proof. rewrite/modulus. by rewrite two_power_nat_equiv. Qed.

  Lemma bitsize_lt_modulus : bitsize < modulus.
  Proof. rewrite modulus_bitsize. exact: Z.pow2_strict. Qed.

  Lemma modulus_min : 2 ≤ modulus.
  Proof.
    rewrite modulus_bitsize -{1}(Z.pow_1_r 2). exact: Z.pow_le_mono_r.
  Qed.

  Lemma modulus_nonzero : modulus ≠ 0.
  Proof. have := modulus_min. lia. Qed.
  #[global] Hint Resolve modulus_nonzero : core.

  Lemma modulus_pos : 0 < modulus.
  Proof. have := modulus_min. lia. Qed.
  #[global] Hint Resolve modulus_pos : core.

  (** [half_modulus] *)

  Definition half_modulus : Z := Z.div2 modulus.
  #[global] Arguments half_modulus : simpl never.

  Lemma half_modulus_modulus : half_modulus = modulus `div` 2.
  Proof. rewrite /half_modulus. by rewrite Z.div2_div. Qed.

  Lemma half_modulus_bitsize : half_modulus = 2 ^ (bitsize - 1).
  Proof.
    rewrite half_modulus_modulus modulus_bitsize.
    by rewrite -Z.div2_div Z.div2_pow2.
  Qed.

  Lemma bitsize_le_half_modulus : bitsize ≤ half_modulus.
  Proof.
    rewrite half_modulus_bitsize Z.log2_up_le_pow2//.
    have := Z.log2_up_lt_lin bitsize ltac:(done). lia.
  Qed.

  Lemma modulus_half_modulus : modulus = 2 * half_modulus.
  Proof.
    rewrite half_modulus_modulus. apply Z.div_exact; first done.
    by rewrite modulus_bitsize Z.pow2_mod2.
  Qed.

  Lemma half_modulus_min : 1 ≤ half_modulus.
  Proof. have := modulus_min. rewrite modulus_half_modulus. lia. Qed.

  Lemma half_modulus_nonzero : half_modulus ≠ 0.
  Proof. have := half_modulus_min. lia. Qed.
  #[global] Hint Resolve half_modulus_nonzero : core.

  Lemma half_modulus_pos : 0 < half_modulus.
  Proof. have := half_modulus_min. lia. Qed.
  #[global] Hint Resolve half_modulus_pos : core.

  (** [is_unsigned], [is_signed], [signed], [testbit] *)

  Definition is_unsigned (z : Z) : Prop :=
    0 ≤ z < modulus.

  Definition is_signed (z : Z) : Prop :=
    let h := half_modulus in - h ≤ z < h.

  Definition signed (x : t) : Z :=
    let y := unsigned x in
    let m := modulus in
    if decide (y < Z.div2 m) then y else y - m.

  Definition testbit (x : t) (i : Z) : bool :=
    Z.testbit (unsigned x) i.

  #[global] Arguments signed : simpl never.
  #[global] Arguments testbit : simpl never.

  Lemma unsigned_range x : Reduce (is_unsigned (unsigned x)).
  Proof. rewrite modulus_bitsize. apply unsigned_range'. Qed.

  Lemma unsigned_repr_modulo z : unsigned (repr z) = z `mod` modulus.
  Proof. rewrite modulus_bitsize. apply unsigned_repr_modulo'. Qed.

  #[global] Hint Resolve unsigned_range repr_unsigned : core.

  Implicit Types (x y : t) (z : Z).

  #[local] Infix "≡" := (Z.eqmod modulus) (only parsing).
  #[local] Notation "(≡)" := (Z.eqmod modulus) (only parsing).

  #[global] Instance unsigned_inj : Inj (=) (=) unsigned.
  Proof. move=>x y H. by rewrite -(repr_unsigned x) -(repr_unsigned y) H. Qed.

  #[global] Instance word_inhabited : Inhabited t.
  Proof. exact (populate (repr 0)). Qed.

  #[global] Instance word_eq_dec : EqDecision t := inj_eq_dec unsigned.

  (** In fact, [t] is a finite type (see ./finite.v). *)
  #[global] Instance word_countable : Countable t :=
    inj_countable' _ _ repr_unsigned.

  (** [repr] *)

  #[global] Instance repr_proper : Proper ((≡) ==> (=)) repr.
  Proof.
    intros z1 z2 ?. apply (inj unsigned). rewrite !unsigned_repr_modulo.
    exact: Z.eqmod_mod_eq.
  Qed.

  #[global] Instance repr_surj : Surj (=) repr.
  Proof. move=>x. by exists (unsigned x). Qed.

  Lemma repr_eq z y : z ≡ unsigned y → repr z = y.
  Proof. by intros ->. Qed.

  #[global] Hint Opaque repr : typeclass_instances.

  (** [unsigned] *)

  (**
  Higher cost than [unsigned_inj], which is more frequently useful.
  *)
  #[global] Instance unsigned_inj_eqmod : Inj (=) (≡) unsigned | 10.
  Proof. move=>x y H. by rewrite -(repr_unsigned x) -(repr_unsigned y) H. Qed.

  Lemma unsigned_repr z : Reduce (is_unsigned z) → unsigned (repr z) = z.
  Proof. intros. by rewrite unsigned_repr_modulo Z.mod_small. Qed.

  Lemma unsigned_repr_eqmod z : unsigned (repr z) ≡ z.
  Proof. by rewrite unsigned_repr_modulo Z.eqmod_mod. Qed.
  #[global] Hint Resolve unsigned_repr_eqmod : core.

  Lemma unsigned_min x : 0 ≤ unsigned x.
  Proof. by destruct (unsigned_range x). Qed.
  #[global] Hint Resolve unsigned_min : core.

  Lemma unsigned_max x : unsigned x < modulus.
  Proof. by destruct (unsigned_range x). Qed.
  #[global] Hint Resolve unsigned_max : core.

  Lemma unsigned_half_modulus x : unsigned x < 2 * half_modulus.
  Proof. by rewrite -modulus_half_modulus. Qed.

  #[global] Hint Opaque unsigned : typeclass_instances.

  (** [signed] *)

  Lemma signed_unsigned x : signed x ≡ unsigned x.
  Proof. rewrite /signed. case_decide. done. exists (-1)%Z; lia. Qed.
  #[global] Hint Resolve signed_unsigned : core.

  Lemma repr_signed x : repr (signed x) = x.
  Proof. by rewrite -[RHS](repr_unsigned x) signed_unsigned. Qed.
  #[global] Hint Resolve repr_signed : core.

  #[global] Instance signed_inj : Inj (=) (=) signed.
  Proof. move=>x y H. by rewrite -(repr_signed x) -(repr_signed y) H. Qed.

  (**
  Higher cost than [signed_inj], which is more frequently useful.
  *)
  #[global] Instance signed_inj_eqmod : Inj (=) (≡) signed | 10.
  Proof. move=>x y H. by rewrite -(repr_signed x) -(repr_signed y) H. Qed.

  Lemma signed_repr_eqmod z : signed (repr z) ≡ z.
  Proof. by rewrite signed_unsigned unsigned_repr_eqmod. Qed.
  #[global] Hint Resolve signed_repr_eqmod : core.

  Lemma signed_repr z : Reduce (is_signed z) → signed (repr z) = z.
  Proof.
    intros. rewrite/signed. case: (decide (0 ≤ z))=>?.
    - rewrite (unsigned_repr z) modulus_half_modulus; last lia.
      rewrite decide_True// Z.div2_div Z.mul_comm Z.div_mul//. lia.
    - set z' := z + modulus. have->: repr z = repr z'.
      { apply repr_eq. rewrite unsigned_repr_eqmod.
        symmetry. exists 1. rewrite/z'. lia. }
      rewrite Z.div2_div (unsigned_repr z') {}/z' modulus_half_modulus;
        last lia.
      rewrite decide_False; first lia.
      rewrite Z.mul_comm Z.div_mul//. lia.
  Qed.

  Lemma signed_range x : Reduce (is_signed (signed x)).
  Proof.
    rewrite/signed -/half_modulus. have := unsigned_range x.
    rewrite modulus_half_modulus. case_decide; lia.
  Qed.

  Lemma signed_min x : - half_modulus ≤ signed x.
  Proof. by destruct (signed_range x). Qed.
  #[global] Hint Resolve signed_min : core.

  Lemma signed_max x : signed x < half_modulus.
  Proof. by destruct (signed_range x). Qed.
  #[global] Hint Resolve signed_max : core.

  #[global] Hint Opaque signed : typeclass_instances.

  (** [testbit] *)

  Lemma testbit_repr z i :
    0 ≤ i < bitsize → testbit (repr z) i = Z.testbit z i.
  Proof.
    apply Z.bits_eq_eqmod; auto.
    by rewrite -modulus_bitsize unsigned_repr_eqmod.
  Qed.

  Lemma bits_eq x y :
    (∀ i, 0 ≤ i < bitsize → testbit x i = testbit y i) → x = y.
  Proof.
    intros. rewrite -(repr_unsigned x) -(repr_unsigned y).
    apply repr_proper. rewrite modulus_bitsize. exact: Z.eqmod_bits_eq.
  Qed.

  Lemma bits_above x i : bitsize ≤ i → testbit x i = false.
  Proof. apply Z.bits_above; auto. by rewrite -modulus_bitsize. Qed.

  Lemma bits_le x y :
    (∀ i, 0 ≤ i < bitsize → testbit x i → testbit y i) →
    unsigned x ≤ unsigned y.
  Proof.
    intros Hxy. apply Z.bits_le; auto=>i Hi Hx.
    destruct (decide (i < bitsize)).
    - by apply: Hxy Hx.
    - rewrite -/(testbit x i) bits_above// in Hx. lia.
  Qed.

  #[local] Hint Resolve Nat.lt_0_succ : core.

  Lemma sign_bit_unsigned x :
    testbit x (bitsize - 1) =
    negb (bool_decide (unsigned x < half_modulus)).
  Proof.
    rewrite half_modulus_bitsize. have [n Hn] : ∃ n, bitsize = S n.
    { have := bitsize_pos. by destruct bitsize; eauto. }
    rewrite Hn Z.sub_1_r -Nat2Z.inj_pred// Nat.pred_succ.
    apply Z.sign_bit; auto. by rewrite -Nat2Z.inj_succ -Hn -modulus_bitsize.
  Qed.

  Lemma bits_signed x i :
    0 ≤ i →
    Z.testbit (signed x) i =
    testbit x (if decide (i < bitsize) then i else bitsize - 1).
  Proof.
    intros Hi. case_decide.
    { apply (Z.bits_eq_eqmod (bitsize)); auto.
      by rewrite -modulus_bitsize signed_unsigned. }
    rewrite /signed sign_bit_unsigned. case_bool_decide.
    - rewrite decide_True//=.
      apply (Z.bits_above (bitsize)); [done| |lia].
      by rewrite -modulus_bitsize.
    - rewrite decide_False//=.
      apply (Z.bits_above_neg (bitsize)); [done| |lia].
      rewrite -modulus_bitsize. have := unsigned_range x. lia.
  Qed.

End WORD_BASE.

(** Small constants *)

Module Type WORD_CONST
  (Import WS : WORD_SIZE)
  (Import WT : WORD_TYPE WS)
  (Import WB : WORD_BASE WS WT).

  Definition zero : t := repr 0.
  Definition one : t := repr 1.
  Definition mone : t := repr (-1).

  #[global] Arguments zero : simpl never.
  #[global] Arguments one : simpl never.
  #[global] Arguments mone : simpl never.

  Module Import const_notation.
    Notation "0" := zero : word_scope.
    Notation "1" := one : word_scope.
    Notation "- 1" := mone : word_scope.
  End const_notation.

  Lemma unsigned_0 : unsigned 0 = 0.
  Proof. by rewrite unsigned_repr_modulo. Qed.
  #[global] Hint Resolve unsigned_0 : core.

  Lemma signed_0 : signed 0 = 0.
  Proof.
    rewrite signed_repr//. have := half_modulus_min. lia.
  Qed.
  #[global] Hint Resolve signed_0 : core.

  Lemma bits_0 i : testbit 0 i = false.
  Proof. by rewrite/testbit unsigned_0 Z.bits_0. Qed.
  #[global] Hint Resolve bits_0 : core.

  Lemma unsigned_1 : unsigned 1 = 1.
  Proof. rewrite unsigned_repr//. have := modulus_min. lia. Qed.
  #[global] Hint Resolve unsigned_1 : core.

  Lemma signed_1 `{BitsizeAtLeast 2} : signed 1 = 1.
  Proof.
    rewrite signed_repr//. split; first by have := half_modulus_min; lia.
    rewrite half_modulus_bitsize -{1}(Z.pow_0_r 2).
    generalize (bitsize_at_least 2)=>?. apply Z.pow_lt_mono_r; lia.
  Qed.

  Lemma bits_1 i : testbit 1 i = bool_decide (i = 0).
  Proof. by rewrite/testbit unsigned_1 -Z.bits_1. Qed.

  Lemma m1_modulo : (-1) `mod` modulus = modulus - 1.
  Proof.
    have->: (-1 = modulus - 1 + -1 * modulus)%Z by lia.
    rewrite Z.mod_add//. apply Z.mod_small. have := modulus_min. lia.
  Qed.

  Lemma unsigned_m1 : unsigned (-1) = modulus - 1.
  Proof. by rewrite unsigned_repr_modulo m1_modulo. Qed.

  Lemma signed_m1 : signed (-1) = -1.
  Proof. rewrite signed_repr//. have := half_modulus_min. lia. Qed.
  #[global] Hint Resolve signed_m1 : core.

  Lemma bits_m1 i : 0 ≤ i < bitsize → testbit (-1) i = true.
  Proof. destruct 1. by rewrite/mone testbit_repr// Z.bits_m1. Qed.

  #[local] Open Scope word_scope.

  Lemma one_nonzero : 1 ≠ 0.
  Proof.
    suff : unsigned 1 ≠ unsigned 0 by congruence.
    by rewrite unsigned_1 unsigned_0.
  Qed.
  #[global] Hint Resolve one_nonzero : core.

  Lemma m1_nonzero : -1 ≠ 0.
  Proof.
    suff : signed (-1) ≠ signed 0 by congruence.
    by rewrite signed_m1 signed_0.
  Qed.
  #[global] Hint Resolve m1_nonzero : core.

  Lemma m1_ne_1 `{BitsizeAtLeast 2} : -1 ≠ 1.
  Proof.
    suff : signed (-1) ≠ signed 1 by congruence.
    by rewrite signed_m1 signed_1.
  Qed.
  #[global] Hint Resolve m1_ne_1 : core.

End WORD_CONST.

(** Addition *)

Module Type WORD_ADD
  (Import WS : WORD_SIZE)
  (Import WT : WORD_TYPE WS)
  (Import WB : WORD_BASE WS WT)
  (Import WC : WORD_CONST WS WT WB).

  Import const_notation.

  Definition opp (x   : t) : t := repr $ - unsigned x.
  Definition add (x y : t) : t := repr $ unsigned x + unsigned y.
  Definition sub (x y : t) : t := repr $ unsigned x - unsigned y.

  #[global] Arguments opp : simpl never.
  #[global] Arguments add : simpl never.
  #[global] Arguments sub : simpl never.

  Module Import add_notation.
    Notation "- x" := (opp x) : word_scope.
    Infix "+" := add : word_scope.
    Infix "-" := sub : word_scope.
  End add_notation.

  Tactic Notation "lift_eq" "by" tactic1(tac) :=
    repeat intro; apply repr_eq; rewrite !unsigned_repr_eqmod; by tac.
  Tactic Notation "lift_eq" uconstr(lem) := lift_eq by rewrite lem.
  Tactic Notation "lift_eq" := lift_eq by idtac.

  (**
  The functions [Zopp], [Zadd], [Zsub] satisfy
  <<
    unsigned (- x) = Zopp modulus (unsigned x)
    unsigned (x + y) = Zadd modulus (unsigned x) (unsigned y)
    unsigned (x - y) = Zsub modulus (unsigned x) (unsigned y)
  >>
  They exist, in part, to feed [zify]. They use [a <? b] rather than
  [bool_decide (a < b)] for efficiency.
  *)

  Definition Zopp (m z : Z) : Z :=
    let d := - z in
    d + (if d <? 0 then m else 0).

  Definition Zadd (m z1 z2 : Z) : Z :=
    let s := z1 + z2 in
    s - (if s <? m then 0 else m).

  Definition Zsub (m z1 z2 : Z) : Z :=
    let d := z1 - z2 in
    d + (if d <? 0 then m else 0).

  (**
  The predicates [Zopp_spec'], [Zadd_spec'], [Zsub_spec'] specify
  [Zopp], [Zadd], [Zsub] using case distinctions [lia] understands.
  They exist, in part, to feed [zify].
  *)

  Definition Zopp_spec' (m z z' : Z) : Prop :=
    let d := - z in
    z ≤ 0 ∧ z' = d ∨
    0 < z ∧ z' = d + m.

  Definition Zadd_spec' (m z1 z2 z' : Z) : Prop :=
    let s := z1 + z2 in
    s < m ∧ z' = s ∨
    m ≤ s ∧ z' = s - m.

  Definition Zsub_spec' (m z1 z2 z' : Z) : Prop :=
    let d := z1 - z2 in
    d < 0 ∧ z' = d + m ∨
    0 ≤ d ∧ z' = d.

  (** [unsigned (x + y)] *)

  Lemma unsigned_add_Zadd x y :
    unsigned (x + y) = Zadd modulus (unsigned x) (unsigned y).
  Proof.
    rewrite/add/Zadd. rewrite unsigned_repr_modulo.
    move: (unsigned_range x) (unsigned_range y)=>??. symmetry.
    case Hc: (_ <? _).
    - apply (Zmod_unique _ _ 0); lia.
    - apply (Zmod_unique _ _ 1); lia.
  Qed.

  Lemma Zadd_spec m z1 z2 : Reduce (Zadd_spec' m z1 z2 (Zadd m z1 z2)).
  Proof. rewrite /Zadd_spec'/Zadd. case Hb: (_ <? _); lia. Qed.

  Lemma unsigned_add_cases x y :
    Reduce (Zadd_spec' modulus (unsigned x) (unsigned y) (unsigned (x + y))).
  Proof. rewrite unsigned_add_Zadd. apply Zadd_spec. Qed.

  (* Corollary that _might_ help manual proofs. *)

  Lemma unsigned_add x y :
    unsigned (x + y) =
    let s := unsigned x + unsigned y in
    let m := modulus in
    s - if bool_decide (s < m) then 0 else m.
  Proof.
    destruct (unsigned_add_cases x y) as [[? ->]|[? ->]]; cbn.
    - by rewrite bool_decide_true// Z.sub_0_r.
    - by rewrite bool_decide_false// Z.nlt_ge.
  Qed.

  (** [unsigned (x - y)] *)

  Lemma unsigned_sub_Zsub x y :
    unsigned (x - y) = Zsub modulus (unsigned x) (unsigned y).
  Proof.
    rewrite/sub/Zsub. rewrite unsigned_repr_modulo.
    move: (unsigned_range x) (unsigned_range y)=>??. symmetry.
    case Hb: (_ <? _).
    - apply (Zmod_unique _ _ (-1)); lia.
    - apply (Zmod_unique _ _ 0); lia.
  Qed.

  Lemma Zsub_spec m z1 z2 : Reduce (Zsub_spec' m z1 z2 (Zsub m z1 z2)).
  Proof. rewrite /Zsub_spec'/Zsub. case Hb: (_ <? _); lia. Qed.

  Lemma unsigned_sub_cases x y :
    Reduce (Zsub_spec' modulus (unsigned x) (unsigned y) (unsigned (x - y))).
  Proof. rewrite unsigned_sub_Zsub. apply Zsub_spec. Qed.

  Lemma unsigned_sub x y :
    unsigned (x - y) =
    let d := unsigned x - unsigned y in
    let m := modulus in
    d + if bool_decide (d < 0) then m else 0.
  Proof.
    destruct (unsigned_sub_cases x y) as [[? ->]|[? ->]]; cbn.
    - by rewrite bool_decide_true//.
    - by rewrite bool_decide_false// ?Z.add_0_r// Z.nlt_ge.
  Qed.

  (** [unsigned (- x)] *)

  Lemma sub_0_l x : (0 - x = - x)%W.
  Proof. lift_eq Z.sub_0_l. Qed.

  Lemma unsigned_opp_Zopp x : unsigned (- x) = Zopp modulus (unsigned x).
  Proof.
    rewrite /Zopp. rewrite -sub_0_l -Z.sub_0_l.
    by rewrite unsigned_sub_Zsub unsigned_0.
  Qed.

  Lemma Zopp_spec m z : Reduce (Zopp_spec' m z (Zopp m z)).
  Proof. rewrite /Zopp_spec'/Zopp. case Hb: (_ <? _); lia. Qed.

  Lemma unsigned_opp_cases' x :
    Reduce (Zopp_spec' modulus (unsigned x) (unsigned (- x))).
  Proof. rewrite unsigned_opp_Zopp. apply Zopp_spec. Qed.

  Lemma unsigned_opp_cases x :
    let u := unsigned x in
    u = 0 ∧ unsigned (- x) = 0
    ∨ 0 < u ∧ unsigned (- x) = modulus - u.
  Proof.
    have := unsigned_opp_cases' x. have := unsigned_min x. lia.
  Qed.

  Lemma unsigned_opp x :
    unsigned (- x) =
    let u := unsigned x in
    if bool_decide (u = 0) then 0 else modulus - u.
  Proof.
    destruct (unsigned_opp_cases x) as [[Hz ->]|[? ->]]; cbn.
    - by rewrite Hz bool_decide_true.
    - rewrite bool_decide_false//. lia.
  Qed.

  #[local] Open Scope word_scope.

  (** [opp] *)

  Lemma repr_opp z : repr (- z) = - repr z.
  Proof. lift_eq. Qed.

  Lemma opp_0 : - 0 = 0.
  Proof. lift_eq. Qed.

  Lemma opp_1 : - 1 = (-1).
  Proof. lift_eq. Qed.

  Lemma opp_m1 : - (-1) = 1.
  Proof. lift_eq. Qed.

  Lemma opp_unsigned x : - x = repr (- unsigned x).
  Proof. done. Qed.

  Lemma opp_signed x : - x = repr (- signed x).
  Proof. apply repr_eq. by rewrite signed_unsigned. Qed.

  Lemma opp_involutive x : - - x = x.
  Proof. lift_eq Z.opp_involutive. Qed.

  #[global] Instance opp_inj : Inj (=) (=) opp.
  Proof. move=>x1 x2 /(f_equal opp). by rewrite !opp_involutive. Qed.

  Lemma opp_inj_wd x y : - x = - y ↔ x = y.
  Proof. split. exact: opp_inj. by intros->. Qed.

  Lemma eq_opp_l x y : - x = y ↔ x = - y.
  Proof. by rewrite -(opp_inj_wd (- x) y) opp_involutive. Qed.

  Lemma eq_opp_r x y : x = - y ↔ - x = y.
  Proof. symmetry. apply eq_opp_l. Qed.

  #[global] Hint Opaque opp : typeclass_instances.

  (** [add], [sub] *)

  Lemma add_unsigned x y : x + y = repr (unsigned x + unsigned y).
  Proof. done. Qed.

  Lemma add_signed x y : x + y = repr (signed x + signed y).
  Proof. by rewrite add_unsigned !signed_unsigned. Qed.

  Lemma sub_unsigned x y : x - y = repr (unsigned x - unsigned y).
  Proof. done. Qed.

  Lemma sub_signed x y : x - y = repr (signed x - signed y).
  Proof. apply repr_eq. by rewrite !signed_unsigned. Qed.

  (** Lots of properties inherited from [Z] *)

  #[global] Instance add_comm : Comm (=) add.
  Proof. lift_eq Z.add_comm. Qed.

  #[global] Instance add_assoc : Assoc (=) add.
  Proof. lift_eq Z.add_assoc. Qed.

  Lemma add_sub_assoc x y z : x + (y - z) = (x + y) - z.
  Proof. lift_eq Z.add_sub_assoc. Qed.

  #[global] Instance add_0_r : RightId (=) 0 add.
  Proof. lift_eq Z.add_0_r. Qed.

  #[global] Instance add_0_l : LeftId (=) 0 add.
  Proof. lift_eq Z.add_0_l. Qed.

  #[global] Instance sub_0_r : RightId (=) 0 (@sub).
  Proof. lift_eq Z.sub_0_r. Qed.

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
    split=>[EQ|->//]. apply unsigned_inj_eqmod.
    apply (f_equal unsigned) in EQ. move: EQ.
    rewrite !unsigned_repr_modulo !Z.mod_eq//.
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

  #[global] Hint Opaque add sub : typeclass_instances.

End WORD_ADD.

(** The theory of a word type *)

Module Type WORD_THEORY
  (WS : WORD_SIZE)
  (WT : WORD_TYPE WS)
:= WORD_BASE WS WT
<+ WORD_CONST WS WT
<+ WORD_ADD WS WT.

(** Any word type and its theory *)

Module Type WORD
:= WORD_SIZE
<+ WORD_TYPE
<+ WORD_THEORY.

(** [Number Notation] support *)

Module Type WORD_AUX_NUM (Import W : WORD).

  Module num.
    Variant num : Set := Num (z : Z).

    (** parse unsigned or signed *)
    Definition uparse (z : Z) : option num :=
      guard (is_unsigned z); Some (Num z).
    Definition iparse (z : Z) : option num :=
      guard (is_signed z); Some (Num z).

    (** print decimal or hexadecimal *)
    Definition dprint '(Num z) : Z := z.
    Definition xprint '(Num z) : Number.int :=
      Number.IntHexadecimal $ Z.to_hex_int z.
  End num.

End WORD_AUX_NUM.

(** [zify] support *)

Module Type WORD_AUX_ZIFY_ARG (Import W : WORD).

  Parameter Inline m : Z.	(** computed [modulus] *)
  Axiom m_spec : m = modulus.
End WORD_AUX_ZIFY_ARG.

Module Type WORD_AUX_ZIFY
  (Import W : WORD)
  (Import WZ : WORD_AUX_ZIFY_ARG W).

  Import Coq.micromega.ZifyClasses.
  Import Coq.micromega.DeclConstant.

  Import const_notation add_notation.

  Implicit Types (x y : t) (z : Z).

  (** Learn [unsigned_range], and support goals [@eq t] *)

  Lemma zify_unsigned_range x : 0 ≤ unsigned x < m.
  Proof. rewrite m_spec. apply unsigned_range. Qed.

  #[global] Instance zify_t : InjTyp t Z := {|
    inj := unsigned;
    pred := fun z => 0 ≤ z < m;
    cstr := zify_unsigned_range;
  |}.
  Add Zify InjTyp zify_t.

  #[global] Instance zify_eq : BinRel (@eq t) := {|
    TR := @eq Z;
    TRInj := fun x y => iff_sym (inj_iff unsigned _ _);
  |}.
  Add Zify BinRel zify_eq.

  Section examples.

    Goal ∀ x : t, x = x.
    Proof. zify. Abort.
    (**
    x : t
    cstr : 0 ≤ unsigned x < m
    ______________________________________
    unsigned x = unsigned x
    *)

  End examples.

  (** Before injecting [opp], let's reproduce an anamoly. *)

  Module bug.
  Section bug.

    Lemma zify_unsigned_opp x : unsigned (- x) = Zopp m (unsigned x).
    Proof. rewrite m_spec. apply unsigned_opp_Zopp. Qed.

    Instance zify_opp : UnOp opp := {|
      TUOp := Zopp m;
      TUOpInj := zify_unsigned_opp;
    |}.
    Add Zify UnOp zify_opp.

    Section examples.

      Goal forall x : t, (- - x = x)%W.
      Proof. zify. Abort.
      (**
      x : t
      cstr : 0 ≤ unsigned x < m
      ______________________________________
      Zopp m (Zopp m (unsigned x)) = unsigned x
      *)

    End examples.

    (** Replace [Zopp m] by cases *)

    Instance zify_opp_spec : UnOpSpec (Zopp m) := {|
      UPred := Zopp_spec' m;
      USpec := Zopp_spec m;
    |}.
    Add Zify UnOpSpec zify_opp_spec.

    Section examples.
      Import Coq.micromega.Zify.
      Goal forall x : t, (- - x = x)%W.
      Proof.
        intros. zify_op.
        (**
        x : t
        cstr : 0 ≤ unsigned x < m
        ______________________________________
        Zopp m (Zopp m (unsigned x)) = unsigned x
        *)

        zify_iter_specs.
        (**
        Error:
        Anomaly "in retyping: Non-functional construction."
        Please report at http://coq.inria.fr/bugs/.
        Raised at file "clib/exninfo.ml" (inlined), line 80, characters 4-11
        Called from file "lib/cErrors.ml" (inlined), line 31, characters 2-44
        Called from file "pretyping/retyping.ml", line 55, characters 23-82
        Called from file "pretyping/retyping.ml" (inlined), line 264, characters 29-55
        Called from file "proofs/tacmach.ml" (inlined), line 111, characters 4-42
        Called from file "proofs/tacmach.ml" (inlined), line 169, characters 28-62
        Called from file "proofs/tacmach.ml" (inlined), line 169, characters 28-62
        Called from file "proofs/tacmach.ml" (inlined), line 169, characters 28-62
        Called from file "tactics/tactics.ml", line 2847, characters 14-45
        Called from file "engine/proofview.ml" (inlined), line 1127, characters 40-46
        Called from file "engine/proofview.ml", line 1132, characters 10-34
        Called from file "engine/proofview.ml" (inlined), line 1131, characters 21-180
        Called from file "engine/proofview.ml" (inlined), line 1131, characters 21-180
        Called from file "engine/logic_monad.ml" (inlined), line 192, characters 38-43
        Called from file "engine/logic_monad.ml" (inlined), line 192, characters 21-63
        Called from file "engine/logic_monad.ml", line 199, characters 65-82
        Called from file "engine/logic_monad.ml", line 260, characters 6-27
        Called from file "engine/logic_monad.ml", line 260, characters 6-27
        Called from file "engine/logic_monad.ml" (inlined), line 192, characters 38-62
        Called from file "engine/logic_monad.ml" (inlined), line 211, characters 60-72
        Called from file "engine/logic_monad.ml", line 67, characters 34-45
        Called from file "engine/logic_monad.ml", line 67, characters 36-42
        Called from file "engine/logic_monad.ml", line 67, characters 36-42
        Called from file "engine/logic_monad.ml", line 67, characters 36-42
        Called from file "engine/logic_monad.ml", line 67, characters 36-42
        Called from file "engine/logic_monad.ml", line 117, characters 8-12
        Called from file "engine/proofview.ml" (inlined), line 234, characters 12-42
        Called from file "proofs/proof.ml", line 381, characters 4-49
        Called from file "proofs/proof.ml", line 567, characters 31-52
        Called from file "vernac/comTactic.ml", line 46, characters 23-59
        Called from file "vernac/declare.ml" (inlined), line 1408, characters 20-33
        Called from file "vernac/comTactic.ml" (inlined), line 43, characters 23-442
        Called from file "vernac/comTactic.ml", line 43, characters 23-442
        Called from file "vernac/vernacinterp.ml" (inlined), line 42, characters 65-74
        Called from file "vernac/vernacstate.ml" (inlined), line 84, characters 30-34
        Called from file "vernac/vernacinterp.ml" (inlined), line 42, characters 15-76
        Called from file "clib/option.ml" (inlined), line 102, characters 19-24
        Called from file "vernac/vernacinterp.ml" (inlined), line 42, characters 4-82
        Called from file "vernac/vernacinterp.ml" (inlined), line 42, characters 4-82
        Called from file "vernac/vernacinterp.ml" (inlined), line 42, characters 15-76
        Called from file "clib/option.ml" (inlined), line 102, characters 19-24
        Called from file "vernac/vernacinterp.ml" (inlined), line 42, characters 4-82
        Called from file "vernac/vernacinterp.ml", line 42, characters 4-82
        Called from file "vernac/vernacinterp.ml", line 213, characters 24-64
        Called from file "lib/flags.ml" (inlined), line 17, characters 14-17
        Called from file "lib/flags.ml" (inlined), line 27, characters 27-82
        Called from file "lib/flags.ml", line 68, characters 20-44
        Re-raised at file "clib/exninfo.ml", line 82, characters 4-38
        Called from file "vernac/vernacinterp.ml" (inlined), line 262, characters 18-43
        Called from file "vernac/vernacinterp.ml" (inlined), line 87, characters 4-7
        Called from file "vernac/vernacinterp.ml" (inlined), line 260, characters 6-279
        Called from file "vernac/vernacinterp.ml" (inlined), line 260, characters 6-279
        Called from file "vernac/vernacinterp.ml" (inlined), line 274, characters 2-57
        Called from file "stm/stm.ml" (inlined), line 1035, characters 4-58
        Called from file "stm/stm.ml", line 2144, characters 20-47
        Re-raised at file "clib/exninfo.ml", line 82, characters 4-38
        Called from file "vernac/vernacinterp.ml" (inlined), line 270, characters 4-22
        Called from file "vernac/vernacinterp.ml" (inlined), line 274, characters 2-57
        Called from file "stm/stm.ml" (inlined), line 1035, characters 4-58
        Called from file "stm/stm.ml", line 2144, characters 20-47
        Called from file "stm/stm.ml" (inlined), line 2141, characters 39-220
        Called from file "stm/stm.ml" (inlined), line 2141, characters 39-220
        Called from file "stm/stm.ml" (inlined), line 2141, characters 39-220
        Called from file "stm/stm.ml" (inlined), line 2141, characters 39-220
        Called from file "stm/stm.ml" (inlined), line 2081, characters 10-14
        Called from file "stm/stm.ml" (inlined), line 2075, characters 23-353
        Called from file "stm/stm.ml" (inlined), line 2075, characters 23-353
        Called from file "stm/stm.ml" (inlined), line 2141, characters 12-220
        Called from file "stm/stm.ml" (inlined), line 2075, characters 23-353
        Called from file "stm/stm.ml" (inlined), line 2075, characters 23-353
        Called from file "stm/stm.ml", line 2141, characters 12-220
        Re-raised at file "stm/stm.ml" (inlined), line 2075, characters 23-353
        Called from file "stm/stm.ml" (inlined), line 2075, characters 23-353
        Called from file "stm/stm.ml", line 2141, characters 12-220
        Called from file "stm/stm.ml", line 956, characters 6-10
        *)
(*
    End examples.
  End bug.
  End bug.

  (** Inject [opp] *)

  Definition zify_Zopp : Z → Z := Zopp m.
  (**
  When using [Zopp m] directly, [zify_iter_specs] throws:

  > Error: Anomaly "Non-functional construction."
  *)

  Lemma zify_unsigned_opp x : unsigned (- x) = zify_Zopp (unsigned x).
  Proof. rewrite /zify_Zopp m_spec. apply unsigned_opp_Zopp. Qed.

  #[global] Program Instance zify_opp : UnOp opp := {|
    TUOp := zify_Zopp;
    TUOpInj := zify_unsigned_opp;
  |}.
  Add Zify UnOp zify_opp.

  Section examples.

    Goal forall x : t, (- - x = x)%W.
    Proof. zify. Abort.
    (**
    x : t
    cstr : 0 ≤ unsigned x < m
    ______________________________________
    zify_Zopp (zify_Zopp (unsigned x)) = unsigned x
    *)

  End examples.

  (** Replace [zify_Zopp] by cases *)

  Lemma zify_Zopp_spec z : Reduce (Zopp_spec' m z (zify_Zopp z)).
  Proof. apply Zopp_spec. Qed.

  #[global] Instance zify_opp_spec : UnOpSpec zify_Zopp := {|
    UPred := Zopp_spec' m;
    USpec := zify_Zopp_spec;
  |}.
  Add Zify UnOpSpec zify_opp_spec.

  Section examples.

    Goal forall x : t, (- - x = x)%W.
    Proof. zify. Abort.
    (**
    x : t
    cstr : 0 ≤ unsigned x < m
    z0 : Z
    H0 : 0 ≤ unsigned x
         → unsigned x = 0 ∧ z0 = 0 ∨ 0 < unsigned x ∧ z0 = m - unsigned x
    z1 : Z
    H1 : 0 ≤ z0 → z0 = 0 ∧ z1 = 0 ∨ 0 < z0 ∧ z1 = m - z0
    ______________________________________
    z1 = unsigned x
    *)

    (** We can prove things with [lia]! *)
    Goal forall x : t, (- - x = x)%W.
    Proof. lia. Abort.

  End examples.
*)
