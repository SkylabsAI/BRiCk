(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.prelude.base.
Require Import bedrock.prelude.word.base.
Require Import bedrock.prelude.word.const.
Require Import bedrock.prelude.word.add.
Require Import bedrock.prelude.word.aux_arg.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

(** Teach [zify] (and [lia]) about word types *)

(**
We use a mixin to register specific word types. This gives us the
opportunity to normalize [word.modulus].
*)

Module Type WORD_ZIFY
  (Import WT : WORD_TYPE)
  (Import WM : WORD_MODULUS WT).

  Import Coq.micromega.ZifyClasses.

  Import base.word const.word add.word.

  Implicit Types (x y : W) (z : Z).

  (**
  Replace [x : W] by [to_Z x : Z], learning [0 ≤ to_Z x < m]
  *)

  Lemma zify_to_Z_range_1 x : 0 ≤ to_Z x < m.
  Proof. rewrite m_spec. apply to_Z_range. Qed.

  #[global] Instance zify_t : InjTyp W Z := {|
    inj := to_Z;
    pred := fun z => 0 ≤ z < m;
    cstr := zify_to_Z_range_1;
  |}.
  Add Zify InjTyp zify_t.

  (** Replace goals [x =@{W} y] by [to_Z x =@{Z} to_Z y] *)

  #[global] Instance zify_eq : BinRel (@eq W) := {|
    TR := @eq Z;
    TRInj := fun x y => iff_sym (inj_iff to_Z _ _);
  |}.
  Add Zify BinRel zify_eq.

  Section examples.

    Goal ∀ x, x = x.
    Proof. zify. Abort.
    (**
    x : word_car W
    cstr : 0 ≤ to_Z x < m
    ______________________________________
    to_Z x = to_Z x
    *)

  End examples.

  (** Replace [opp] by [Zopp m] *)

  Definition zify_Zopp : Z → Z := Zopp m.

  Lemma zify_to_Z_opp x : to_Z (- x) = zify_Zopp (to_Z x).
  Proof. by rewrite to_Z_opp_Zopp -m_spec. Qed.

  #[global] Instance zify_opp : UnOp opp := {|
    TUOp := zify_Zopp;
    TUOpInj := zify_to_Z_opp;
  |}.
  Add Zify UnOp zify_opp.

  Section examples.

    Goal ∀ x, (- - x = x)%W.
    Proof. zify. Abort.
    (**
    x : word_car W
    cstr : 0 ≤ to_Z x < m
    ______________________________________
    zify_Zopp (zify_Zopp (to_Z x)) = to_Z x
    *)

  End examples.

  (** Replace [Zopp m] by cases [lia] understands *)

  Lemma zify_Zopp_cases z : Reduce (opp_cases m z (zify_Zopp z)).
  Proof. apply Zopp_cases. Qed.

  #[global] Instance zify_opp_cases : UnOpSpec zify_Zopp := {|
    UPred := opp_cases m;
    USpec := zify_Zopp_cases;
  |}.
  Add Zify UnOpSpec zify_opp_cases.

  Section examples.

    Goal ∀ x, (- - x = x)%W.
    Proof. zify. Abort.
    (**
    x : word_car W
    cstr : 0 ≤ to_Z x < m
    z0 : Z
    H0 : to_Z x = 0 ∧ z0 = 0 ∨ to_Z x ≠ 0 ∧ z0 = m - to_Z x
    z1 : Z
    H1 : z0 = 0 ∧ z1 = 0 ∨ z0 ≠ 0 ∧ z1 = m - z0
    ______________________________________
    z1 = to_Z x
    *)

    (** [lia] can prove things! *)

    Goal ∀ x, (- - x = x)%W.
    Proof. lia. Abort.

  End examples.

  (**
  Replace words [0], [1], [-1] by integers [0], [1], [m - 1]
  *)

  #[global] Instance zify_0 : CstOp 0%W := {|
    TCstInj := to_Z_0 W;
  |}.
  Add Zify CstOp zify_0.

  #[global] Instance zify_1 : CstOp 1%W := {|
    TCstInj := to_Z_1 W;
  |}.
  Add Zify CstOp zify_1.

  Lemma zify_to_Z_m1 : to_Z (W:=W) (-1) = m - 1.
  Proof. by rewrite m_spec to_Z_m1. Qed.

  #[global] Instance zify_m1 : CstOp (-1)%W := {|
    TCstInj := zify_to_Z_m1;
  |}.
  Add Zify CstOp zify_m1.

  Section examples.

    Goal (- 0 =@{W} 0)%W.
    Proof. zify. Abort.
    (**
    z0 : Z
    H0 : 0 = 0 ∧ z0 = 0 ∨ 0 ≠ 0 ∧ z0 = m - 0
    ______________________________________
    z0 = 0
    *)
    Goal (- 0 =@{W} 0)%W.
    Proof. lia. Abort.

    Goal (- 0 ≠@{W} 1)%W.
    Proof. zify. Abort.
    (**
    z0 : Z
    H0 : 0 = 0 ∧ z0 = 0 ∨ 0 ≠ 0 ∧ z0 = m - 0
    ______________________________________
    z0 ≠ 1
    *)
    Goal (- 0 ≠@{W} 1)%W.
    Proof. lia. Abort.

    Goal (- (1) =@{W} (-1))%W.
    Proof. zify. Abort.
    (**
    z0 : Z
    H0 : 1 = 0 ∧ z0 = 0 ∨ 1 ≠ 0 ∧ z0 = m - 1
    ______________________________________
    z0 = m - 1
    *)
    Goal (- (1) =@{W} (-1))%W.
    Proof. lia. Abort.

    Goal (-1 ≠@{W} 0)%W.
    Proof. zify. Abort.
    (**
    ______________________________________
    m - 1 ≠ 0
    *)

  End examples.

  (** Replace [add] by [Zadd m] *)

  Definition zify_Zadd : Z → Z → Z := Zadd m.

  Lemma zify_to_Z_add x y :
    to_Z (x + y) = zify_Zadd (to_Z x) (to_Z y).
  Proof. by rewrite to_Z_add_Zadd -m_spec. Qed.

  #[global] Instance zify_add : BinOp add := {|
    TBOp := zify_Zadd;
    TBOpInj := zify_to_Z_add;
  |}.
  Add Zify BinOp zify_add.

  Section examples.

    Goal ∀ x, (x + (-x) = 0)%W.
    Proof. zify. Abort.
    (**
    x : word_car W
    cstr : 0 ≤ to_Z x < m
    z0 : Z
    H0 : to_Z x = 0 ∧ z0 = 0 ∨ to_Z x ≠ 0 ∧ z0 = m - to_Z x
    ______________________________________
    zify_Zadd (to_Z x) z0 = 0
    *)

  End examples.

  (** Replace [Zadd m] by cases *)

  Lemma zify_Zadd_cases z1 z2 : Reduce (add_cases m z1 z2 (zify_Zadd z1 z2)).
  Proof. apply Zadd_cases. Qed.

  #[global] Instance zify_add_cases : BinOpSpec zify_Zadd := {|
    BPred := add_cases m;
    BSpec := zify_Zadd_cases;
  |}.
  Add Zify BinOpSpec zify_add_cases.

  Section examples.

    Goal ∀ x, (x + (-x) = 0)%W.
    Proof. zify. Abort.
    (**
    x : word_car W
    cstr : 0 ≤ to_Z x < m
    z0 : Z
    H0 : to_Z x = 0 ∧ z0 = 0 ∨ to_Z x ≠ 0 ∧ z0 = m - to_Z x
    z1 : Z
    H1 : to_Z x + z0 < m ∧ z1 = to_Z x + z0
         ∨ m ≤ to_Z x + z0 ∧ z1 = to_Z x + z0 - m
    ______________________________________
    z1 = 0
    *)
    Goal ∀ x, (x + (-x) = 0)%W.
    Proof. lia. Abort.

    Goal ∀ x y, (x + y = y + x)%W.
    Proof. lia. Qed.

  End examples.

  (** Replace [sub] by [Zsub m] *)

  Definition zify_Zsub : Z → Z → Z := Zsub m.

  Lemma zify_to_Z_sub x y : to_Z (x - y) = zify_Zsub (to_Z x) (to_Z y).
  Proof. by rewrite to_Z_sub_Zsub -m_spec. Qed.

  #[global] Instance zify_sub : BinOp sub := {|
    TBOp := zify_Zsub;
    TBOpInj := zify_to_Z_sub;
  |}.
  Add Zify BinOp zify_sub.

  (** Replace [Zsub m] by cases *)

  Lemma zify_Zsub_cases z1 z2 : Reduce (sub_cases m z1 z2 (zify_Zsub z1 z2)).
  Proof. apply Zsub_cases. Qed.

  #[global] Instance zify_sub_cases : BinOpSpec zify_Zsub := {|
    BPred := sub_cases m;
    BSpec := zify_Zsub_cases;
  |}.
  Add Zify BinOpSpec zify_sub_cases.

  Section examples.

    Goal ∀ x y z : W, (x - (y + z) = (x - y) - z)%W.
    Proof. zify. Abort.
    (**
    x, y, z : word_car W
    cstr : 0 ≤ to_Z y < m
    cstr0 : 0 ≤ to_Z z < m
    cstr1 : 0 ≤ to_Z x < m
    z2 : Z
    H2 : to_Z x - to_Z y < 0 ∧ z2 = to_Z x - to_Z y + m
         ∨ 0 ≤ to_Z x - to_Z y ∧ z2 = to_Z x - to_Z y
    z3 : Z
    H3 : z2 - to_Z z < 0 ∧ z3 = z2 - to_Z z + m
         ∨ 0 ≤ z2 - to_Z z ∧ z3 = z2 - to_Z z
    z4 : Z
    H4 : to_Z y + to_Z z < m ∧ z4 = to_Z y + to_Z z
         ∨ m ≤ to_Z y + to_Z z ∧ z4 = to_Z y + to_Z z - m
    z5 : Z
    H5 : to_Z x - z4 < 0 ∧ z5 = to_Z x - z4 + m
         ∨ 0 ≤ to_Z x - z4 ∧ z5 = to_Z x - z4
    ______________________________________
    z5 = z3
    *)
    Goal ∀ x y z : W, (x - (y + z) = (x - y) - z)%W.
    Proof. lia. Abort.

    Goal ∀ x y z : W, ((x + y) - (z + x) = y - z)%W.
    Proof. lia. Abort.

  End examples.

  (**
  TODO (PDS): Study the code and document this properly.

  According to the preceding explanation of [UnOp] (and [BinOp] for
  that matter), the following instance would instruct [zify] to
  replace [to_Z] by [to_Z], serving no purpose.

  In fact, [zify] uses each operator instance differently based on a
  simple classification. Consider [@UnOp S1 S2 T1 T2 (op : S1 -> S2)
  (_ : InjTyp S1 T1) (_ : InjType S2 T2)] so that [TUOp : T1 -> T2].
  Then, [zify]'s classification for such an instance is (trying the
  rules in this order):

  - [OpInj]: if [op] is convertible to [TUOp] (as decided by the
  pretyping function Reductionops.is_conv)

  - [OpSame]: if [op] is alpha equivalent to its [TUOp] (as decided by
  EConstr.eq_constr)

  - [OpConv]: if [op' : S1 -> T2 := fun s => inj (op s)] is
  convertible to [top' := fun s => TUOp (inj s)]

  - [OpOther]: otherwise

  [zify] classifies the following instance as [OpInj], and the
  preceding [UnOp] instance for [opp] differently.

  The _effect_ of the following instance is, in part, to enable [zify]
  to relate integers like [0 : Z] and injections like [to_Z 0 : Z] by
  stripping away the injection. Consider the goal [0 =@{Z} to_Z 0].
  Prior to registering the instance, [zify] has no effect on that
  goal. After registering the instance, [zify] changes it to [0 =@{Z}
  0].
  *)

  Section examples_before.

    Goal 0 = to_Z (W:=W) 0.
    Proof. zify. Abort.
    (**
    ______________________________________
    0 = to_Z 0
    *)

    Goal 0 ≠ to_Z (W:=W) 1.
    Proof. zify. Abort.
    (**
    ______________________________________
    0 ≠ to_Z 1
    *)

  End examples_before.

  #[global] Program Instance zify_to_Z : UnOp to_Z := {|
    TUOp := fun z => z;
    TUOpInj := fun x => eq_refl;
  |}.
  Add Zify UnOp zify_to_Z.

  Section examples_after.

    Goal 0 = to_Z (W:=W) 0.
    Proof. zify. Abort.
    (**
    ______________________________________
    0 = 0
    *)
    Goal 0 = to_Z (W:=W) 0.
    Proof. lia. Abort.

    Goal 0 ≠ to_Z (W:=W) 1.
    Proof. zify. Abort.
    (**
    ______________________________________
    0 ≠ 1
    *)

  End examples_after.

  (** Lia already knows about goals [iff] *)

  Section examples.

    Goal ∀ x y c : W, (c + x = c + y ↔ x = y)%W.
    Proof. lia. Abort.

  End examples.

  (**
  Replace [to_Z (of_Z W z)] by [z `mod` m]. With [Ltac
  Zify.zify_convert_to_euclidean_division_equations_flag ::=
  constr:(true).], [zify] can (slowly) eliminate occurrences of
  [Z.modulo], enabling [lia] to solve such goals.

  Note: Literals arising from number notation are handled separately
  to avoid spurious applications of [Z.modulo]. See ./aux.v.
  *)

  Lemma zify_to_of_Z z : to_Z (of_Z W z) = z `mod` m.
  Proof. by rewrite m_spec to_of_Z_modulo. Qed.

  #[global] Program Instance zify_of_Z : UnOp (of_Z W) := {|
    TUOp := fun z => z `mod` m;
    TUOpInj := zify_to_of_Z;
  |}.
  Add Zify UnOp zify_of_Z.

End WORD_ZIFY.
