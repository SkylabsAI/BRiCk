(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.pmap.
Require Import stdpp.fin_maps.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.prelude.stdpp_ssreflect.

Lemma N_div_eucl_lt_spec (b q r : N) :
  (r < b)%N → N.div_eucl (b * q + r)%N b = (q, r).
Proof.
  (* Proof by Olivier Laurent on Zulip. *)
  intro Hr.
  rewrite (surjective_pairing (N.div_eucl (b * q + r) b)).
  symmetry. f_equal.
  - exact (N.div_unique _ _ _ _ Hr eq_refl).
  - exact (N.mod_unique _ _ _ _ Hr eq_refl).
Qed.

Definition Byte_of_N_total (n : N) : Byte.byte :=
  match Byte.of_N n with
  | Some b => b
  | None   => Byte.x00
  end.

Lemma Byte_of_N_is_Some (n : N) : (n < 256)%N -> is_Some (Byte.of_N n).
Proof.
  move => H. rewrite /Byte.of_N. repeat case_match.
  all: first [by eexists | lia].
Qed.

Fixpoint BS_repeat_x00 (n : nat) : bs :=
  match n with
  | O   => BS.EmptyString
  | S n => BS.String "000"%byte (BS_repeat_x00 n)
  end.

Lemma BS_append_nil_r (s : bs) : BS.append s "" = s.
Proof. induction s as [|b s IH]; [done | by rewrite /= IH]. Qed.

Module Pairing.
  Definition Pos_double_succ_N (n : N) : positive :=
    match n with
    | N.pos n => xI n
    | _       => xH
    end.

  Definition encode (nm : N * N) : positive :=
    (Pos.shiftl 1%positive nm.1 * Pos_double_succ_N nm.2)%positive.

  Fixpoint decode_aux (n : N) (p : positive) : N * N :=
    match p with
    | xO p => decode_aux (N.succ n) p
    | xI p => (n, N.pos p)
    | _    => (n, 0%N)
    end.
  Definition decode (p : positive) : N * N := decode_aux 0%N p.

  Lemma decode_aux_pow2 (n : N) (p : positive) :
    decode_aux n (2 ^ p) = (n + N.pos p, 0)%N.
  Proof.
    revert n. induction p as [|p IH] using Pos.peano_ind => n.
    { by rewrite N.add_1_r. }
    rewrite Pos.pow_succ_r.
    rewrite /={}IH. f_equal.
    rewrite -N.add_1_r -N.add_assoc. f_equal.
    by rewrite N.add_1_l.
  Qed.

  Lemma decode_aux_pos_spec (n : N) (pn pm : positive) :
    decode_aux n (2 ^ pn * pm~1) = (n + N.pos pn, N.pos pm)%N.
  Proof.
    revert n; induction pn as [|pn IH] using Pos.peano_ind => n.
    { by rewrite /=N.add_1_r. }
    rewrite Pos.pow_succ_r.
    rewrite /={}IH. f_equal.
    rewrite -N.add_1_r -N.add_assoc. f_equal.
    by rewrite N.add_1_l.
  Qed.

  Lemma decode_encode (nm : N * N) : decode (encode nm) = nm.
  Proof.
    destruct nm as [n m]. rewrite /encode/=.
    destruct n as [|pn]; destruct m as [|pm] => //=.
    + rewrite Pos.mul_1_r. rewrite /decode. apply decode_aux_pow2.
    + rewrite /decode. by rewrite decode_aux_pos_spec.
  Qed.


  Lemma decode_aux_acc_wf (p : positive) (acc n m : N) :
    decode_aux acc p = (n, m) → (acc ≤ n)%N.
  Proof.
    revert acc n m; induction p as [p IH|p IH|] => acc n m /=.
    - move => /= [<- _] //.
    - move => /IH. lia.
    - move => /= [<- _] //.
  Qed.

  Definition Pos_lt_wf := Wf_nat.well_founded_ltof positive Pos.to_nat.

  Lemma decode_aux_pow2_invert (n : N) (p e : positive) :
    decode_aux n p = (n + N.pos e, 0)%N → (2 ^ e)%positive = p.
  Proof.
    revert n p.
    induction e as [e IH] using (well_founded_induction Pos_lt_wf) => n p.
    destruct p as [p|p|]. 1,3: move => []; lia.
    destruct e as [|e _] using Pos.peano_ind => /=.
    - rewrite Pos.pow_1_r/= N.add_1_r.
      destruct p as [p|p|]. 1,3: done.
      move => /=/decode_aux_acc_wf. lia.
    - move => H.
      rewrite Pos.pow_succ_r. apply Pos.mul_cancel_l.
      eapply IH; first (rewrite /ltof/=; lia).
      erewrite H. f_equal. lia.
  Qed.

  Lemma encode_decode_aux (n : N) (p pn pm : positive) :
    decode_aux n p = (n + N.pos pn, N.pos pm)%N → (2 ^ pn * pm~1)%positive = p.
  Proof.
    revert n p pm.
    induction pn as [pn IH] using (well_founded_induction Pos_lt_wf) => n p pm.
    destruct p as [p|p|]. 1,3: move => []; lia. move => /=.
    destruct pn as [|pn _] using Pos.peano_ind => /=.
    - rewrite Pos.pow_1_r/= N.add_1_r.
      destruct p as [p|p|] => /=. 1,3: move => []; lia.
      move => /=/decode_aux_acc_wf. lia.
    - move => H.
      rewrite Pos.pow_succ_r -Pos.mul_assoc.
      apply Pos.mul_cancel_l.
      eapply IH; first (rewrite /ltof/=; lia).
      erewrite H. f_equal. lia.
  Qed.

  Lemma encode_decode (p : positive) : encode (decode p) = p.
    destruct (decode p) as [n m] eqn:H; revert H.
    rewrite /encode/decode/=.
    destruct n as [|pn]; destruct m as [|pm] => /=.
    - rewrite Pos.mul_1_l. destruct p => /=; [done| |done].
      move => /decode_aux_acc_wf. lia.
    - rewrite Pos.mul_1_l. destruct p => /=; [by move => [->]| |done].
      move => /decode_aux_acc_wf. lia.
    - rewrite Pos.mul_1_r. apply: decode_aux_pow2_invert.
    - apply: encode_decode_aux.
  Qed.
End Pairing.

Module BSAsPos.
  #[local] Open Scope N.

  Fixpoint strip_trailing_x00 (s : bs) : N * bs :=
    match s with
    | BS.EmptyString => (0%N, s)
    | BS.String b s  =>
        let '(n, s) := strip_trailing_x00 s in
        match (Byte.eqb b "000"%byte, s) with
        | (true, ""%bs) => (N.succ n, s)
        | _             => (n, BS.String b s)
        end
    end.

  Lemma strip_trailing_x00_repeat (n : N) :
    strip_trailing_x00 (BS_repeat_x00 (N.to_nat n)) = (n, ""%bs).
  Proof.
    induction n as [|n IH] using N.peano_ind => /=; first done.
    by rewrite N2Nat.inj_succ /= IH.
  Qed.

  Lemma strip_trailing_x00_append_repeat_x00 (s : bs) (n : N) :
    let '(k, s') := strip_trailing_x00 s in
    strip_trailing_x00 (s ++ BS_repeat_x00 (N.to_nat n)) = (k + n, s').
  Proof.
    rewrite (surjective_pairing (strip_trailing_x00 s)).
    revert n; induction s as [|b s IH] => n /=.
    - by rewrite strip_trailing_x00_repeat N.add_0_l.
    - rewrite {}IH. repeat case_match; simpl in *; simplify_eq => //.
      by rewrite N.add_succ_l.
  Qed.

  (* encode_aux [b1; b2; b3] = (3, b3b2b1) *)
  (* encode_aux [b1; b2; b3; 00; 00] = (5, 0000b3b2b1) *)
  Fixpoint encode_length_aux (s : bs) : N * N :=
    match s with
    | BS.EmptyString => (0, 0)
    | BS.String b s  =>
        let '(len, e) := encode_length_aux s in
        (N.succ len, Byte.to_N b + N.shiftl e 8)
    end.
  Definition encode_aux (s : bs) : N :=
    (encode_length_aux s).2.
  Definition encode (s : bs) : positive :=
    let '(n, s) := strip_trailing_x00 s in
    let e := encode_aux s in
    Pairing.encode (n, e).

  Fixpoint decode_length_aux (len : nat) (e : N) : bs :=
    match len with
    | O     => ""%bs
    | S len =>
        let q := N.shiftr e 8 in
        let r := N.land e 255 in
        let b := Byte_of_N_total r in
        BS.String b (decode_length_aux len q)
    end.
  Definition encoded_length (n : N) : N :=
    let bits := N.log2_up n in
    let q := N.shiftr bits 3 in
    let r := N.land bits 7 in
    if r is 0%N then q else N.succ q.
  Definition decode_aux (e : N) : bs :=
    let len := encoded_length e in
    decode_length_aux (N.to_nat len) e.
  Definition decode (p : positive) : bs :=
    let '(n, e) := Pairing.decode p in
    let s := decode_aux e in
    match n with
    | 0%N => s
    | _   => BS.append s (BS_repeat_x00 (N.to_nat n))
    end.

  Lemma decode_encode_aux (s0 s : bs) (n : N) :
    strip_trailing_x00 s0 = (n, s) →
    (decode_aux (encode_aux s) ++ BS_repeat_x00 (N.to_nat n))%bs = s0.
  Proof.
  Admitted.

  Lemma encode_decode_aux (n : N) :
    encode_aux (decode_aux n) = n.
  Proof.
  Admitted.

  Lemma strip_trailing_x00_decode_aux (e : N) :
    strip_trailing_x00 (decode_aux e) = (0%N, decode_aux e).
  Proof.
    remember (decode_aux e) as s eqn:Hs; revert e Hs.
    induction s as [|b s IH] => e /= H; first done.
  Admitted.

  Lemma decode_encode (s : bs) : decode (encode s) = s.
  Proof.
    rewrite /encode/decode.
    destruct (strip_trailing_x00 s) as [n s0] eqn:Hstrip.
    rewrite Pairing.decode_encode.
    destruct n as [|p].
    - move: Hstrip => /decode_encode_aux/= <-.
      by rewrite BS_append_nil_r.
    - by apply decode_encode_aux.
  Qed.

  Lemma encode_decode (p : positive) : encode (decode p) = p.
  Proof.
    rewrite /encode/decode.
    destruct (Pairing.decode p) as [n e] eqn:Hdec.
    destruct n as [|np].
    - rewrite strip_trailing_x00_decode_aux.
      rewrite encode_decode_aux.
      by rewrite -Hdec Pairing.encode_decode.
    - move: (strip_trailing_x00_append_repeat_x00 (decode_aux e) (Npos np)).
      destruct (strip_trailing_x00 (decode_aux e)) as [k s'] eqn:Hstrip.
      move => ->.
      move: (Pairing.encode_decode p); rewrite {}Hdec => <-; f_equal.
      have {2}->: (N.pos np = 0 + N.pos np)%N by lia.
      apply pair_eq. rewrite N.add_cancel_r.
      move: (strip_trailing_x00_decode_aux e). rewrite Hstrip.
      move => [] ? ?. subst k s'. by rewrite encode_decode_aux.
  Qed.

  Lemma encode_as_decode (s : bs) (p : positive) : decode p = s → p = encode s.
  Proof. move => H. rewrite -(encode_decode p) H. done. Qed.

  Definition decode_Some (p : positive) : option bs :=
    Some (decode p).
End BSAsPos.


#[local] Remove Hints bytestring_countable : typeclass_instances.

#[global, program]
Instance bs_countable : Countable bs := {|
  encode := BSAsPos.encode;
  decode := BSAsPos.decode_Some;
|}.
Next Obligation.
  move => ?. rewrite /BSAsPos.decode_Some/=.
  f_equal; apply BSAsPos.decode_encode.
Qed.


Record bs_map {V : Type} := mkBSMap { bs_pmap : Pmap V }.
Arguments bs_map : clear implicits.

#[global] Instance bs_map_fmap : FMap bs_map := fun _ _ f m =>
  {| bs_pmap := fmap f (m.(bs_pmap)) |}.

#[global] Instance bs_map_lookup (A : Type) : Lookup bs A (bs_map A) := fun k m =>
  lookup (encode k) m.(bs_pmap).

#[global] Instance bs_map_empty (A : Type) : Empty (bs_map A) :=
  {| bs_pmap := empty |}.

#[global] Instance bs_map_partial_alter (A : Type) : PartialAlter bs A (bs_map A) := fun f k m =>
  {| bs_pmap := partial_alter f (encode k) m.(bs_pmap) |}.

#[global] Instance bs_map_omap : OMap bs_map := fun _ _ f m =>
  {| bs_pmap := omap f m.(bs_pmap) |}.

#[global] Instance bs_map_merge : Merge bs_map := fun _ _ _ f m1 m2 =>
  {| bs_pmap := merge f m1.(bs_pmap) m2.(bs_pmap) |}.

#[global] Instance bs_map_map_fold (V : Type) : MapFold bs V (bs_map V) := fun _ f acc m =>
  let f (k : positive) (v : V) acc :=
    match decode k with
    | None => acc
    | Some k => f k v acc
    end
  in
  map_fold f acc m.(bs_pmap).

#[global] Instance bs_map_finmap : FinMap BS.t bs_map.
Proof.
  constructor.
  - move => ? [m1][m2]. rewrite /lookup/bs_map_lookup.
    move => H. f_equal. apply map_eq. move => i.
    destruct (@decode bs _ _ i) as [s|] eqn:Heq.
    + enough (i = encode s) by by subst i. move: Heq.
      rewrite /decode/encode/=/BSAsPos.decode_Some.
      move => []. apply BSAsPos.encode_as_decode.
    + exfalso. by rewrite /decode/=/BSAsPos.decode_Some in Heq.
  - done.
  - move => *. rewrite /lookup/bs_map_lookup. apply lookup_partial_alter.
  - move => ??? i1 i2 H. rewrite /lookup/bs_map_lookup. apply lookup_partial_alter_ne.
    move => Heq. apply H.
    have: (@decode bs _ _ (encode i1) = decode (encode i2)) by rewrite Heq.
    rewrite !decode_encode => [][]//.
  - move => *. rewrite /fmap/bs_map_fmap/lookup/bs_map_lookup. apply lookup_fmap.
  - move => *. rewrite /omap/bs_map_omap/lookup/bs_map_lookup. apply lookup_omap.
  - move => *. rewrite /merge/bs_map_merge/lookup/bs_map_lookup. apply lookup_merge.
  - move => A B P f b.
    rewrite /map_fold/bs_map_map_fold/lookup/bs_map_lookup.
    rewrite /empty/bs_map_empty/insert/map_insert/partial_alter/bs_map_partial_alter.
    move => H1 H2 [m].
    apply: (map_fold_ind (fun b m => P b {| bs_pmap := m |})); [done|].
    rewrite /insert/map_insert.
    move => i v m0 r P1 P2. case_match eqn:Hi.
    + have Hdec: i = encode t.
      { move: Hi. rewrite /decode/encode/=/BSAsPos.decode_Some.
        move => []. apply BSAsPos.encode_as_decode. }
      rewrite Hdec in P1 |- *. apply (H2 _ _ {| bs_pmap := m0 |} _ P1 P2).
    + exfalso. move: Hi. by rewrite /decode/=/BSAsPos.decode_Some.
Qed.
