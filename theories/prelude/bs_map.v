(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.pmap.
Require Import stdpp.fin_maps.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.prelude.stdpp_ssreflect.

Module Pairing.
  Definition Pos_powN (p : positive) (n : N) : positive :=
    match n with
    | N.pos n => Pos.pow p n
    | _       => 1%positive
    end.

  Definition Pos_double_and_add_1N (n : N) : positive :=
    match n with
    | N.pos n => xI n
    | _       => xH
    end.

  Definition encode (nm : N * N) : positive :=
    (Pos_powN 2 nm.1 * Pos_double_and_add_1N nm.2)%positive.

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
  Fixpoint encode_aux (s : bs) : N * N :=
    match s with
    | BS.EmptyString => (0%N, 0%N)
    | BS.String b s =>
        let '(len, e) := encode_aux s in
        (N.succ len, 256 * e + Byte.to_N b)%N
    end.
  Definition encode (s : bs) : positive := Pairing.encode (encode_aux s).

  Fixpoint decode_aux (len : nat) (e : N) : bs :=
    match len with
    | 0%nat => BS.EmptyString
    | S len =>
        let '(q, r) := N.div_eucl e 256%N in
        let b :=
          match Byte.of_N r with
          | Some b => b
          | None   => Byte.x00 (* Unreachable. *)
          end
        in
        BS.String b (decode_aux len q)
    end.
  Definition decode (p : positive) : bs :=
    let (len, e) := Pairing.decode p in
    decode_aux (N.to_nat len) e.

  Definition decode_Some (p : positive) : option bs :=
    Some (decode p).

  Goal True.
    assert (let s := "Hello, world!"%bs in decode (encode s) = s); [done|].
  Abort.

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

  Lemma decode_encode_aux (s : bs) (len e : N) :
    encode_aux s = (len, e) → decode_aux (N.to_nat len) e = s.
  Proof.
    revert e s; induction len as [|len IH] using N.peano_ind => e s.
    - destruct s as [|b s]; first done. simpl.
      destruct (encode_aux s) as [??].
      move => []. lia.
    - destruct s as [|b s] => /=; first (move => []; lia).
      destruct (encode_aux s) as [len' e'] eqn:Heq.
      rewrite N2Nat.inj_succ/=.
      destruct (N.div_eucl e 256) as [q r] eqn:Hdiv.
      move => [] /N.succ_inj ? ?. subst len' e.
      rewrite N_div_eucl_lt_spec in Hdiv; last first.
      { rewrite /Byte.to_N; case_match; lia. }
      move: Hdiv => [<-<-].
      rewrite Byte.of_to_N. f_equal. by apply IH.
  Qed.

  Eval vm_compute in decode_aux 0%nat 2%N.

  Lemma encode_decode_aux (len e : N) :
    encode_aux (decode_aux (N.to_nat len) e) = (len, e).
  Proof.
    (* FIXME false when [len = 0] *)
  Admitted.

  Lemma decode_encode (s : bs) : decode (encode s) = s.
  Proof.
    rewrite /encode/decode/=.
    destruct (encode_aux s) as [len e] eqn:Henc.
    rewrite Pairing.decode_encode.
    by apply decode_encode_aux.
  Qed.

  Lemma encode_decode (p : positive) : encode (decode p) = p.
    rewrite /encode/decode/=.
    destruct (Pairing.decode p) as [len e] eqn:Hdec.
    rewrite encode_decode_aux -Hdec.
    apply Pairing.encode_decode.
  Qed.

  Lemma encode_as_decode (s : bs) (p : positive) : decode p = s → p = encode s.
  Proof. move => H. rewrite -(encode_decode p) H. done. Qed.
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
