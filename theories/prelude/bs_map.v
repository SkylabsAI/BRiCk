(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.pmap.
Require Import stdpp.fin_maps.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.prelude.stdpp_ssreflect.

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

Require Import Coq.Program.Wf.

Definition log256 (n : N) : N := N.log2 n / 8.

Fixpoint enc_and_lengthN (s : bs) : N * N :=
  match s with
  | BS.EmptyString => (0%N, 0%N)
  | BS.String b s =>
      let '(e, len) := enc_and_lengthN s in
      (N.succ (Byte.to_N b) * 256 ^ len + e, N.succ len)%N
  end.
Definition enc (s : bs) : N := (enc_and_lengthN s).1.

Goal True.
  assert (enc (BS.parse []) = 0%N) as _ by reflexivity.
  assert (enc (BS.parse [Byte.x00]) = 1%N) as _ by reflexivity.
  assert (enc (BS.parse [Byte.x01]) = 2%N) as _ by reflexivity.
  assert (enc (BS.parse [Byte.xff]) = 256%N) as _ by reflexivity.
  assert (enc (BS.parse [Byte.x00; Byte.x00]) = 257%N) as _ by reflexivity.
  assert (enc (BS.parse [Byte.x00; Byte.x01]) = 258%N) as _ by reflexivity.
  assert (enc (BS.parse [Byte.xff; Byte.xff]) = 65792%N) as _ by reflexivity.
  assert (enc (BS.parse [Byte.x00; Byte.x00; Byte.x00]) = 65793%N) as _ by reflexivity.
Abort.

Definition byte_of_N (n : N) : Byte.byte :=
  match Byte.of_N n with
  | None => Byte.x00
  | Some b => b
  end.

Fixpoint all_ff_pos (p : positive) : bs :=
  match p with
  | xH => BS.String Byte.xff BS.EmptyString
  | xI p => let s := all_ff_pos p in BS.String Byte.xff (BS.append s s)
  | xO p => let s := all_ff_pos p in BS.append s s
  end.
Definition all_ff (n : N) : bs :=
  match n with
  | N0 => BS.EmptyString
  | Npos p => all_ff_pos p
  end.

Lemma N_lt_acc (n : N) : Acc N.lt n.
  apply (N.strong_right_induction _ 0); last exact (N.le_0_l n).
  move => m H IH.
  constructor => k Hk.
  refine (IH k (N.le_0_l k) Hk).
Defined.

#[local] Set Transparent Obligations.

Program Fixpoint dec (n : N) {wf N.lt n} : bs :=
  let len := log256 n in (* The string has either [len] or [len+1] characters. *)
  let qr := N.div_eucl n (256 ^ len) in
  match qr.1 with
  | 0%N =>
    match qr.2 with
    | 0%N => BS.EmptyString
    | r   => BS.String (byte_of_N (N.pred r)) BS.EmptyString
    end
  | q   =>
    match qr.2 with
    | 0%N => all_ff len
    | r   => BS.String (byte_of_N (N.pred r)) (dec q)
    end
  end.
Next Obligation. done. Defined.
Next Obligation.
  move => n _ len qr s1 s2 Hq ? s3 s4 Hr ?; subst len s1 s2 s3 s4.
  revert qr Hq Hr.
  have := N.div_eucl_spec n (256 ^ log256 n).
  destruct (N.div_eucl n (256 ^ log256 n)) as [q r] => Heq.
  move => qr; subst qr; move => /= Hq Hr. rewrite {}Heq.
  assert (1 ≤ 256 ^ log256 n)%N as Hlem1 by lia.
  assert (1 * q + r ≤ 256 ^ log256 n * q + r)%N as Hlem2.
  { by apply N.add_le_mono_r, N.mul_le_mono_r. }
  revert Hlem1 Hlem2.
  generalize (2 ^ log256 n)%N. lia.
Defined.
Next Obligation. done. Defined.
Next Obligation. done. Defined.
Next Obligation. refine (wf_guard 1000%nat N_lt_acc). Defined.

Eval vm_compute in log256 0%N.
Eval vm_compute in N.div_eucl 0%N (256 ^ 0%N)%N.
Eval vm_compute in enc "Hello, world!"%bs.
(* Set Printing All. *)
Eval vm_compute in dec 0%N.
Eval vm_compute in dec 1%N.

Eval vm_compute in log256 1%N.
Eval vm_compute in N.div_eucl 1%N (256 ^ 0)%N.
Eval vm_compute in N.div_eucl 1%N (256 ^ 0)%N.


Axiom bs_decode_total : forall (i : positive), @decode bs _ _ i ≠ None.
Axiom bs_decode_surj : forall (i : positive) (b : bs), decode i = Some b → i = encode b.

#[global] Instance bs_map_finmap : FinMap BS.t bs_map.
Proof.
  constructor.
  - move => ? [m1][m2]. rewrite /lookup/bs_map_lookup/=.
    move => H. f_equal. apply map_eq. move => i.
    destruct (@decode bs _ _ i) eqn:Heq.
    + apply bs_decode_surj in Heq. subst i. done.
    + exfalso. by apply (bs_decode_total i).
  - done.
  - move => *. rewrite /lookup/bs_map_lookup/=. apply lookup_partial_alter.
  - move => ??? i1 i2 H. rewrite /lookup/bs_map_lookup/=. apply lookup_partial_alter_ne.
    move => Heq. apply H.
    have: (@decode bs _ _ (encode i1) = decode (encode i2)) by rewrite Heq.
    rewrite !decode_encode => [][]//.
  - move => *. rewrite /fmap/bs_map_fmap/lookup/bs_map_lookup/=. apply lookup_fmap.
  - move => *. rewrite /omap/bs_map_omap/lookup/bs_map_lookup/=. apply lookup_omap.
  - move => *. rewrite /merge/bs_map_merge/lookup/bs_map_lookup/=. apply lookup_merge.
  - move => A B P f b.
    rewrite /map_fold/bs_map_map_fold/lookup/bs_map_lookup.
    rewrite /empty/bs_map_empty/insert/map_insert/partial_alter/bs_map_partial_alter/=.
    move => H1 H2 [m]/=.
    apply: (map_fold_ind (fun b m => P b {| bs_pmap := m |})); [done|].
    rewrite /insert/map_insert/=.
    move => i v m0 r P1 P2. case_match.
    + have Hi: i = encode t by apply bs_decode_surj.
      rewrite Hi in P1 |- *. apply (H2 _ _ {| bs_pmap := m0 |} _ P1 P2).
    + exfalso. move: H. clear. apply bs_decode_total.
Qed.
