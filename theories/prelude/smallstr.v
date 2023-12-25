(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Structures.OrderedType.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.uint63.
Require Import bedrock.prelude.array.
Require Import Coq.Strings.Byte.
Require Coq.Strings.String.
Require Import Coq.Lists.List.
Require Coq.Numbers.BinNums.

Import Uint63 PArray.


Module SmallStr.
(* Encoding of strings using packed bits
 * the first word is the length
 * NOTE because we only have 63 bits available,
 * we only store 7 bytes rather than 8
 *)
#[projections(primitive=yes)]
Record t : Set := Smallstr { smallstr_bytes : array Uint63.int }.
#[global] Notation smallstr := t.

Definition bit (n : Uint63.int) (b : bool) : Uint63.int :=
  if b
  then Uint63.lsl 1%int63 n
  else 0%int63.

Section with_notation.
  Import BinNums String Ascii.
  #[local] Infix "b|" := Uint63.lor (at level 30).
  Fixpoint nat_to_int (n : nat) (acc : Uint63.int) : Uint63.int :=
    match n with
    | 0 => acc
    | S n => nat_to_int n (Uint63.add acc 1)
    end.

  Fixpoint pos_to_int (p : positive) (acc : Uint63.int) : Uint63.int :=
    match p with
    | xH => acc
    | xI p => pos_to_int p ((Uint63.lsl acc 1) b| 1)
    | xO p => pos_to_int p (Uint63.lsl acc 1)
    end.

  Search byte N.
  Definition to_int (a : Byte.byte) : Uint63.int :=
    of_Z (BinIntDef.Z.of_N (to_N a)).

  #[local]
  Definition int_to_nat (i : int) : nat := BinIntDef.Z.to_nat (to_Z i).
  #[local]
  Definition int_to_byte (i : int) : Byte.byte :=
    match of_N (BinIntDef.Z.to_N (to_Z i)) with
    | None => x00
    | Some x => x
    end.

End with_notation.

#[local]
Fixpoint next_string (acc : Uint63.int) (n : nat) (s : list Byte.byte) : Uint63.int * list Byte.byte :=
  match n , s with
  | S n , List.cons b s =>
    next_string (Uint63.add (Uint63.lsl acc 8%int63) (to_int b)) n s
  | _ , nil => (acc, s)
  | 0%nat , s => (acc, s)
  end.

Definition parse (s : list Byte.byte) : smallstr :=
  let n := List.length s in
  let len := nat_to_int n 0 in
  let empty := make (((6+7) + len) / 7)%uint63 0%uint63 in
  let arr := set empty 0 len in
  Smallstr ((fix populate from n s arr :=
     match s with
     | nil => arr
     | s => let (v,s) := next_string 0 7 s in
           match n with
           | 0 => arr
           | S n => populate (1 + from)%uint63 n s (set arr from v)
           end
     end) 1%int63 n s arr).

Definition print (s : smallstr) : list Byte.byte :=
  let s := s.(smallstr_bytes) in
  let len := get s 0%uint63 in
  let len_nat := int_to_nat len in
  let int_min a b := if leb a b then a else b in
  let shift (len : int) : int := (8 * (int_min len 7 - 1))%uint63 in
  (fix go rest (resti : int) i (r : int) byte :=
     match rest with
     | 0 => nil
     | S rest =>
       let resti := (resti - 1)%uint63 in
       let a := int_to_byte (Uint63.land (Uint63.lsr byte r) 255) in
       let '(nexti, nextr, byte) :=
         if is_zero r
         then (* go to the next byte *)
           (i + 1, shift resti, get s i)
         else (* shift 8 fewer bits in this byte *)
           (i, r - 8, byte)
       in
       a :: go rest resti nexti nextr byte
     end)%uint63 len_nat len 2%uint63 (shift len) (get s 1).

Import BinInt.


#[program]
Definition eq_dec s1 s2 : Decision (s1 = s2) :=
  match PArray.eq_dec s1.(smallstr_bytes) s2.(smallstr_bytes) with
  | left _ => left _
  | right _ => right _
  end.
Next Obligation. intros [] []. simpl. now intros ->. Qed.
Next Obligation. intros [] []. simpl. intros H E. apply H. now injection E. Qed.

Definition eqb (s1 s2 : smallstr) := match eq_dec s1 s2 with left _ => true | _ => false end.

#[global] Instance smallstr_eqdec : EqDecision smallstr := eq_dec.


Definition compare s1 s2 :=
  (PArray.compare (cmp:=Uint63.compare) s1.(smallstr_bytes) s2.(smallstr_bytes)).

Definition lt s1 s2 :=
  @PArray.lt _ eq (fun x y => to_Z x < to_Z y)%Z (fun x y => to_Z x > to_Z y)%Z
             s1.(smallstr_bytes) s2.(smallstr_bytes).

Lemma eq'_eq (a1 a2 : array _) :
  (@eq' _ eq (fun x y => to_Z x < to_Z y)%Z (fun x y => to_Z x > to_Z y)%Z) a1 a2 <-> a1 = a2.
Proof.
  split.
  - inversion 1. apply array_ext => //. rewrite !default_get !H1 H0 //.
  - move => ->. by constructor.
Qed.

Instance Uint63_spec_compare_Z x y:
  SpecCompare (x = y) (to_Z x < to_Z y)%Z (to_Z x > to_Z y)%Z (x ?= y)%uint63.
Proof.
  rewrite Uint63.compare_spec.
  constructor; case Z.compare_spec => //=; lia.
Qed.

Existing Class CompareSpec.
Existing Instance Uint63.compare_spec_Z.

Lemma uint63_compare_swap :
  ∀ x y : int, inv (x ?= y)%uint63 = (y ?= x)%uint63.
Proof.
  intros. rewrite !Uint63.compare_spec.
  do 2!case: Z.compare_spec => //=; lia.
Qed.

#[global] Instance compare_spec s1 s2 : CompareSpec (s1 = s2) (lt s1 s2) (lt s2 s1) (compare s1 s2).
Proof.
  destruct s1 as [a1], s2 as [a2] => /=.
  rewrite /lt/gt /compare /=.
  induction (PArray.compare_spec _ _ a1 a2); constructor; auto.
  - f_equal. by apply eq'_eq.
  - apply/rel_cmp_iff.
    suff ->: Lt = PArray.compare (cmp:=Uint63.compare) a2 a1.
    { apply pre_rel_spec. }
    symmetry.
    apply sc_gt in H.
    rewrite compare_swap.
    { by case: PArray.compare H. }
    apply uint63_compare_swap.
Qed.


#[global] Instance spec_compare s1 s2 : SpecCompare (s1 = s2) (lt s1 s2) (lt s2 s1) (compare s1 s2).
Proof.
  destruct s1 as [a1], s2 as [a2] => /=.
  constructor.
  - injection 1. rewrite /compare /= => H1. apply sc_eq. by apply/eq'_eq.
  - rewrite /lt. move/rel_cmp_iff/spec_pre_rel => //=.
  - rewrite /lt /compare. move/rel_cmp_iff/spec_pre_rel => //= H.
    rewrite PArray.compare_swap -?H //.
    apply uint63_compare_swap.
Qed.

#[global] Instance lt_Irreflexive : Irreflexive lt.
Proof.
  intros s => +.
  unfold lt,compare.
  inversion 1; lia.
Qed.

(* #[global] Instance : Transitive gt. *)
(* Proof. *)
(*   intros [a1] [a2] [a3]. *)
(*   rewrite /gt /compare /=. *)
(*   have H: forall x y, Uint63.compare x y = inv (Uint63.compare y x). *)
(*   { intros. rewrite !Uint63.compare_spec. repeat case : Z.compare_spec => //=; lia. } *)
(*   move/(compare_swap_aux H) => ?. *)
(*   move/(compare_swap_aux H) => ?. *)
(*   apply (compare_swap_aux H). *)
(*   cbn in *. *)
(*   apply (lt_Transitive (Smallstr a3) (Smallstr a2) (Smallstr a1)) => //. *)
(* Qed. *)

#[local] Definition to_list (s : smallstr) : (int * list Uint63.int) :=
  PArray.to_list (s.(smallstr_bytes)).

#[local] Definition of_list (l : int * list Uint63.int) : option smallstr :=
  match PArray.of_list l with Some a => Some (Smallstr a) | _ => None end.

#[global,program] Instance smallstr_countable : Countable smallstr :=
  { encode s := encode s.(smallstr_bytes);
    decode l := option_map (Smallstr) (decode l)
  }.
Next Obligation.
  move => [a].
  by rewrite decode_encode.
Qed.
End SmallStr.

#[global] Declare Scope smallstr_scope.
#[global] Delimit Scope smallstr_scope with smallstr.
#[global] Bind Scope smallstr_scope with SmallStr.smallstr.
#[global] String Notation SmallStr.smallstr SmallStr.parse SmallStr.print : smallstr_scope.

(* Unset Printing Notations. *)
Eval lazy in SmallStr.smallstr_bytes "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".

Instructions Eval lazy in SmallStr.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf" "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".
(*  9788956 *)
(* 15416266 *)
Instructions Eval vm_compute in SmallStr.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf" "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".
(*  8146865 *)
(* 14891156 *)


Module Type TEST.
  Import Coq.Strings.String.
  Definition sanity (s : string) :=
    if String.eqb (string_of_list_byte (SmallStr.print (SmallStr.parse (list_byte_of_string s)))) s then True else False.

  Succeed Example _1 : sanity "a" := I.
  Succeed Example _1 : sanity "ab" := I.
  Succeed Example _1 : sanity "abc" := I.
  Succeed Example _1 : sanity "abcd" := I.
  Succeed Example _1 : sanity "abcde" := I.
  Succeed Example _1 : sanity "abcdef" := I.
  Succeed Example _1 : sanity "abcdefg" := I.
  Succeed Example _1 : sanity "abcdefgh" := I.
  Succeed Example _1 : sanity "abcdefghi" := I.
  Example _1 : sanity "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf" := I.

Instructions Eval lazy in String.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string.
(* 15418213 *)

Instructions Eval vm_compute in String.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string.
(* 14892062 *)

  Time Eval vm_compute in sanity "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".
 (* 60175911 *)
 (* 9256064  *)
End TEST.


Module OT_SmallStr <: OrderedType.OrderedType.
  Definition t := SmallStr.t.
  Definition eq := @eq SmallStr.t.
  Definition lt := SmallStr.lt.

  Implicit Types s : SmallStr.t.

  Lemma eq_refl s : eq s s.
  Proof. reflexivity. Qed.
  Lemma eq_sym s1 s2 : eq s1 s2 -> eq s2 s1.
  Proof. by symmetry. Qed.

  Lemma eq_trans s1 s2 s3 : eq s1 s2 -> eq s2 s3 -> eq s1 s3.
  Proof. intros *->->. reflexivity. Qed.

  Lemma lt_trans s1 s2 s3: lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof.
    apply: PArray.lt_Transitive; [|lia..].
    intros x y z ? ?. lia.
  Qed.

  Lemma lt_not_eq : forall (x y : t) (_ : lt x y), not (eq x y).
  Proof. intros * H1 ->. by apply: SmallStr.lt_Irreflexive. Qed.

  #[program]
  Definition compare s1 s2 : Compare lt eq s1 s2 :=
    match SmallStr.compare s1 s2 as c return
          SmallStr.compare s1 s2 = c -> Compare lt eq s1 s2
  with
    | Lt => fun H => LT _
    | Eq => fun H => EQ _
    | Gt => fun H => GT _
    end (Logic.eq_refl (SmallStr.compare s1 s2)).
  Next Obligation. move => ? ?. case: SmallStr.compare_spec => //. Qed.
  Next Obligation. move => ? ?. case: SmallStr.compare_spec => //. Qed.
  Next Obligation. move => ? ?. case: SmallStr.compare_spec => //. Qed.

  #[program]
  Definition eq_dec := SmallStr.eq_dec.
End OT_SmallStr.
