(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From stdpp Require Export gmap mapset.
From stdpp Require Import pmap.
From bedrock.prelude Require Import base fin_sets.

(* To upstream to Iris: using [mapseq_eq] directly would unfold a TC opaque
definition and interfere with TC search. *)
Lemma gset_eq `{Countable A} (X1 X2 : gset A) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof. apply mapset_eq. Qed.

(** [set_map] specialized to [gset]; avoids awkward type annotations such as
[set_map (C := gset _) (D := gset _)].
*)
#[global] Notation gset_map := (set_map (C := gset _) (D := gset _)) (only parsing).

#[global] Notation gset_concat_map :=
  (set_concat_map (C := gset _) (D := gset _)) (only parsing).

(* Like [set_concat_map], but purely in terms of gsets.
*)
Section gset_bind.
  Context `{Countable A} `{Countable B}.

  Definition gset_bind (f : A → gset B) (xs : gset A) : gset B :=
    gset_concat_map (elements ∘ f) xs.

  Lemma gset_bind_empty f :
    gset_bind f ∅ = ∅.
  Proof. done. Qed.

  Lemma elem_of_gset_bind f b xs :
    b ∈ gset_bind f xs ↔ ∃ x, x ∈ xs ∧ b ∈ f x.
  Proof. set_solver. Qed.

  #[global] Instance set_unfold_gset_bind f b xs P Q :
    (∀ x, SetUnfoldElemOf x xs (P x)) → (∀ x, SetUnfoldElemOf b (f x) (Q x)) →
    SetUnfoldElemOf b (gset_bind f xs) (∃ x, P x ∧ Q x).
  Proof. constructor. rewrite elem_of_gset_bind. set_solver. Qed.

  Lemma gset_bind_union f xs1 xs2 :
    gset_bind f (xs1 ∪ xs2) =
    gset_bind f xs1 ∪ gset_bind f xs2.
  Proof. set_solver. Qed.

  Lemma gset_bind_singleton f a :
    gset_bind f {[ a ]} = f a.
  Proof. set_solver. Qed.
End gset_bind.

(* Tactic for more efficiently computing a gmap (suggested by Robbert Krebbers). *)
Module compute_gmap.
  Definition to_pmap {K V : Type} `{Countable K} : gmap K V -> Pmap V :=
    map_fold (fun k v pm => <[encode k := v]> pm) ∅.

  Definition of_pmap {K V : Type} `{Countable K} : Pmap V -> gmap K V :=
    map_fold (fun k v m =>
      match decode k with
      | None => m
      | Some k => <[k := v]> m
      end) ∅.

  Lemma insert_to_pmap_lookup_Some_decode {K V : Type} `{Countable K}
      (k : K) (v : V) (m : gmap K V) (j : positive) (w : V) :
    <[encode k:=v]> (to_pmap m) !! j = Some w → ∃ k, @encode K _ _ k = j.
  Proof.
    move => /lookup_insert_Some [].
    { move => [??]. simplify_eq.  by eexists. }
    move => [_]. clear. rewrite /to_pmap.
    elim m using map_ind; clear; first done.
    move => k v m Hk IH.
    rewrite map_fold_insert //.
    - move => /lookup_insert_Some [][??]; [by eexists|by apply IH].
    - move => ????? Hne *. apply insert_commute => ?. simplify_eq.
  Qed.

  Lemma to_of_pmap {K V : Type} `{Countable K} :
    forall (m : gmap K V), of_pmap (to_pmap m) = m.
  Proof.
    move => m. rewrite /of_pmap/to_pmap.
    elim m using map_ind; clear m; first done.
    move => k v m Hk IH. rewrite -{2}IH{IH}.
    rewrite !map_fold_insert; [by rewrite decode_encode|..|done].
    - move => j1 j2 ??? Hne H1 H2.
      apply insert_to_pmap_lookup_Some_decode in H1 as [k1 H1].
      apply insert_to_pmap_lookup_Some_decode in H2 as [k2 H2].
      repeat case_match => //.
      rewrite insert_commute // => ?. simplify_eq.
      rewrite ->decode_encode in *. simplify_eq.
    - revert Hk. elim m using map_ind; first done.
      move => ???? IH /lookup_insert_None [??].
      rewrite map_fold_insert => //; intros.
      + rewrite lookup_insert_ne //. apply IH => //.
        move => Habs. by apply encode_inj in Habs.
      + rewrite insert_commute; first done.
        move => Habs. by apply encode_inj in Habs.
    - move => *. rewrite insert_commute; first done.
      move => Habs. by apply encode_inj in Habs.
  Qed.

  Ltac compute_gmap t :=
    let ty := type of t in
    let ty := eval hnf in ty in
    lazymatch ty with
    | gmap ?K ?V =>
        let t := eval vm_compute in (@to_pmap K V _ _ t) in
        let t :=
          eval lazy [
            of_pmap map_fold Pmap_fold pmap.Pmap_fold_aux pmap.Pmap_ne_fold
          ] in (@of_pmap K V _ _ t)
        in t
    end.
End compute_gmap.
