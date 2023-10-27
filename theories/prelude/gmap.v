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

From stdpp Require Export countable infinite fin_maps fin_map_dom.
From stdpp Require Import mapset pmap.
From stdpp Require Import options.

Local Open Scope positive_scope.

Module Type COUNTABLE.
  Parameter K : Type.
  Parameter eq_dec : EqDecision K.
  Parameter countable : @Countable K eq_dec.
End COUNTABLE.

(* This functor is a based on a copy of the stdpp gmap implementation. *)
Module GMap (Import Countable : COUNTABLE).

  Local Notation "P ~ 0" := (λ p, P p~0) : function_scope.
  Local Notation "P ~ 1" := (λ p, P p~1) : function_scope.
  Implicit Type P : positive → Prop.

  (** * The tree data structure *)
  Inductive gmap_dep_ne (A : Type) (P : positive → Prop) :=
    | GNode001 : gmap_dep_ne A P~1  → gmap_dep_ne A P
    | GNode010 : P 1 → A → gmap_dep_ne A P
    | GNode011 : P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P
    | GNode100 : gmap_dep_ne A P~0 → gmap_dep_ne A P
    | GNode101 : gmap_dep_ne A P~0 → gmap_dep_ne A P~1 → gmap_dep_ne A P
    | GNode110 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P
    | GNode111 : gmap_dep_ne A P~0 → P 1 → A → gmap_dep_ne A P~1 → gmap_dep_ne A P.
  Global Arguments GNode001 {A P} _ : assert.
  Global Arguments GNode010 {A P} _ _ : assert.
  Global Arguments GNode011 {A P} _ _ _ : assert.
  Global Arguments GNode100 {A P} _ : assert.
  Global Arguments GNode101 {A P} _ _ : assert.
  Global Arguments GNode110 {A P} _ _ _ : assert.
  Global Arguments GNode111 {A P} _ _ _ _ : assert.

  (** Using [Variant] we supress the generation of the induction scheme. We use
  the induction scheme [gmap_ind] in terms of the smart constructors to reduce the
  number of cases, similar to Appel and Leroy. *)
  Variant gmap_dep (A : Type) (P : positive → Prop) :=
    | GEmpty : gmap_dep A P
    | GNodes : gmap_dep_ne A P → gmap_dep A P.
  Global Arguments GEmpty {A P}.
  Global Arguments GNodes {A P} _.

  Existing Instance eq_dec.
  Existing Instance countable.

  Record gmap_key (q : positive) :=
    GMapKey { _ : encode (A:=K) <$> decode q = Some q }.
  Global Arguments GMapKey {_} _.

  Lemma gmap_key_encode (k : K) : gmap_key (encode k).
  Proof. constructor. by rewrite decode_encode. Qed.
  Global Instance gmap_key_pi q : ProofIrrel (gmap_key q).
  Proof. intros [?] [?]. f_equal. apply (proof_irrel _). Qed.

  Record gmap A := GMap { gmap_car : gmap_dep A gmap_key }.
  Global Arguments GMap {_} _.
  Global Arguments gmap_car {_} _.

  Global Instance gmap_dep_ne_eq_dec {A P} :
    EqDecision A → (∀ i, ProofIrrel (P i)) → EqDecision (gmap_dep_ne A P).
  Proof.
    intros ? Hirr t1 t2. revert P t1 t2 Hirr.
    refine (fix go {P} (t1 t2 : gmap_dep_ne A P) {Hirr : _} : Decision (t1 = t2) :=
      match t1, t2 with
      | GNode001 r1, GNode001 r2 => cast_if (go r1 r2)
      | GNode010 _ x1, GNode010 _ x2 => cast_if (decide (x1 = x2))
      | GNode011 _ x1 r1, GNode011 _ x2 r2 =>
         cast_if_and (decide (x1 = x2)) (go r1 r2)
      | GNode100 l1, GNode100 l2 => cast_if (go l1 l2)
      | GNode101 l1 r1, GNode101 l2 r2 => cast_if_and (go l1 l2) (go r1 r2)
      | GNode110 l1 _ x1, GNode110 l2 _ x2 =>
         cast_if_and (go l1 l2) (decide (x1 = x2))
      | GNode111 l1 _ x1 r1, GNode111 l2 _ x2 r2 =>
         cast_if_and3 (go l1 l2) (decide (x1 = x2)) (go r1 r2)
      | _, _ => right _
      end);
      clear go; abstract first [congruence|f_equal; done || apply Hirr|idtac].
  Defined.
  Global Instance gmap_dep_eq_dec {A P} :
    (∀ i, ProofIrrel (P i)) → EqDecision A → EqDecision (gmap_dep A P).
  Proof. intros. solve_decision. Defined.
  Global Instance gmap_eq_dec {A} :
    EqDecision A → EqDecision (gmap A).
  Proof. intros. solve_decision. Defined.

  (** The smart constructor [GNode] and eliminator [gmap_dep_ne_case] are used to
  reduce the number of cases, similar to Appel and Leroy. *)
  Local Definition GNode {A P}
      (ml : gmap_dep A P~0)
      (mx : option (P 1 * A)) (mr : gmap_dep A P~1) : gmap_dep A P :=
    match ml, mx, mr with
    | GEmpty, None, GEmpty => GEmpty
    | GEmpty, None, GNodes r => GNodes (GNode001 r)
    | GEmpty, Some (p,x), GEmpty => GNodes (GNode010 p x)
    | GEmpty, Some (p,x), GNodes r => GNodes (GNode011 p x r)
    | GNodes l, None, GEmpty => GNodes (GNode100 l)
    | GNodes l, None, GNodes r => GNodes (GNode101 l r)
    | GNodes l, Some (p,x), GEmpty => GNodes (GNode110 l p x)
    | GNodes l, Some (p,x), GNodes r => GNodes (GNode111 l p x r)
    end.

  Local Definition gmap_dep_ne_case {A P B} (t : gmap_dep_ne A P)
      (f : gmap_dep A P~0 → option (P 1 * A) → gmap_dep A P~1 → B) : B :=
    match t with
    | GNode001 r => f GEmpty None (GNodes r)
    | GNode010 p x => f GEmpty (Some (p,x)) GEmpty
    | GNode011 p x r => f GEmpty (Some (p,x)) (GNodes r)
    | GNode100 l => f (GNodes l) None GEmpty
    | GNode101 l r => f (GNodes l) None (GNodes r)
    | GNode110 l p x => f (GNodes l) (Some (p,x)) GEmpty
    | GNode111 l p x r => f (GNodes l) (Some (p,x)) (GNodes r)
    end.

  (** Operations *)
  Local Definition gmap_dep_ne_lookup {A} : ∀ {P}, positive → gmap_dep_ne A P → option A :=
    fix go {P} i t {struct t} :=
    match t, i with
    | (GNode010 _ x | GNode011 _ x _ | GNode110 _ _ x | GNode111 _ _ x _), 1 => Some x
    | (GNode100 l | GNode110 l _ _ | GNode101 l _ | GNode111 l _ _ _), i~0 => go i l
    | (GNode001 r | GNode011 _ _ r | GNode101 _ r | GNode111 _ _ _ r), i~1 => go i r
    | _, _ => None
    end.
  Local Definition gmap_dep_lookup {A P}
      (i : positive) (mt : gmap_dep A P) : option A :=
    match mt with GEmpty => None | GNodes t => gmap_dep_ne_lookup i t end.
  Global Instance gmap_lookup {A} :
      Lookup K A (gmap A) := λ k mt,
    gmap_dep_lookup (encode k) (gmap_car mt).

  Global Instance gmap_empty {A} : Empty (gmap A) := GMap GEmpty.

  (** Block reduction, even on concrete [gmap]s.
  Marking [gmap_empty] as [simpl never] would not be enough, because of
  https://github.com/coq/coq/issues/2972 and
  https://github.com/coq/coq/issues/2986.
  And marking [gmap] consumers as [simpl never] does not work either, see:
  https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/171#note_53216 *)
  Global Opaque gmap_empty.

  Local Fixpoint gmap_dep_ne_singleton {A P} (i : positive) :
      P i → A → gmap_dep_ne A P :=
    match i with
    | 1 => GNode010
    | i~0 => λ p x, GNode100 (gmap_dep_ne_singleton i p x)
    | i~1 => λ p x, GNode001 (gmap_dep_ne_singleton i p x)
    end.

  Local Definition gmap_partial_alter_aux {A P}
      (go : ∀ i, P i → gmap_dep_ne A P → gmap_dep A P)
      (f : option A → option A) (i : positive) (p : P i)
      (mt : gmap_dep A P) : gmap_dep A P :=
    match mt with
    | GEmpty =>
       match f None with
       | None => GEmpty | Some x => GNodes (gmap_dep_ne_singleton i p x)
       end
    | GNodes t => go i p t
    end.
  Local Definition gmap_dep_ne_partial_alter {A} (f : option A → option A) :
      ∀ {P} (i : positive), P i → gmap_dep_ne A P → gmap_dep A P :=
    Eval lazy -[gmap_dep_ne_singleton] in
    fix go {P} i p t {struct t} :=
      gmap_dep_ne_case t $ λ ml mx mr,
        match i with
        | 1 => λ p, GNode ml ((p,.) <$> f (snd <$> mx)) mr
        | i~0 => λ p, GNode (gmap_partial_alter_aux go f i p ml) mx mr
        | i~1 => λ p, GNode ml mx (gmap_partial_alter_aux go f i p mr)
        end p.
  Local Definition gmap_dep_partial_alter {A P}
      (f : option A → option A) : ∀ i : positive, P i → gmap_dep A P → gmap_dep A P :=
    gmap_partial_alter_aux (gmap_dep_ne_partial_alter f) f.
  Global Instance gmap_partial_alter {A} :
      PartialAlter K A (gmap A) := λ f k '(GMap mt),
    GMap $ gmap_dep_partial_alter f (encode k) (gmap_key_encode k) mt.

  Local Definition gmap_dep_ne_fmap {A B} (f : A → B) :
      ∀ {P}, gmap_dep_ne A P → gmap_dep_ne B P :=
    fix go {P} t :=
      match t with
      | GNode001 r => GNode001 (go r)
      | GNode010 p x => GNode010 p (f x)
      | GNode011 p x r => GNode011 p (f x) (go r)
      | GNode100 l => GNode100 (go l)
      | GNode101 l r => GNode101 (go l) (go r)
      | GNode110 l p x => GNode110 (go l) p (f x)
      | GNode111 l p x r => GNode111 (go l) p (f x) (go r)
      end.
  Local Definition gmap_dep_fmap {A B P} (f : A → B)
      (mt : gmap_dep A P) : gmap_dep B P :=
    match mt with GEmpty => GEmpty | GNodes t => GNodes (gmap_dep_ne_fmap f t) end.
  Global Instance gmap_fmap : FMap (gmap) := λ {A B} f '(GMap mt),
    GMap $ gmap_dep_fmap f mt.

  Local Definition gmap_dep_omap_aux {A B P}
      (go : gmap_dep_ne A P → gmap_dep B P) (tm : gmap_dep A P) : gmap_dep B P :=
    match tm with GEmpty => GEmpty | GNodes t' => go t' end.
  Local Definition gmap_dep_ne_omap {A B} (f : A → option B) :
      ∀ {P}, gmap_dep_ne A P → gmap_dep B P :=
    fix go {P} t :=
      gmap_dep_ne_case t $ λ ml mx mr,
        GNode (gmap_dep_omap_aux go ml) ('(p,x) ← mx; (p,.) <$> f x)
              (gmap_dep_omap_aux go mr).
  Local Definition gmap_dep_omap {A B P} (f : A → option B) :
    gmap_dep A P → gmap_dep B P := gmap_dep_omap_aux (gmap_dep_ne_omap f).
  Global Instance gmap_omap : OMap (gmap) := λ {A B} f '(GMap mt),
    GMap $ gmap_dep_omap f mt.

  Local Definition gmap_merge_aux {A B C P}
      (go : gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P)
      (f : option A → option B → option C)
      (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) : gmap_dep C P :=
    match mt1, mt2 with
    | GEmpty, GEmpty => GEmpty
    | GNodes t1', GEmpty => gmap_dep_ne_omap (λ x, f (Some x) None) t1'
    | GEmpty, GNodes t2' => gmap_dep_ne_omap (λ x, f None (Some x)) t2'
    | GNodes t1', GNodes t2' => go t1' t2'
    end.

  Local Definition diag_None' {A B C} {P : Prop}
      (f : option A → option B → option C)
      (mx : option (P * A)) (my : option (P * B)) : option (P * C) :=
    match mx, my with
    | None, None => None
    | Some (p,x), None => (p,.) <$> f (Some x) None
    | None, Some (p,y) => (p,.) <$> f None (Some y)
    | Some (p,x), Some (_,y) => (p,.) <$> f (Some x) (Some y)
    end.

  Local Definition gmap_dep_ne_merge {A B C} (f : option A → option B → option C) :
      ∀ {P}, gmap_dep_ne A P → gmap_dep_ne B P → gmap_dep C P :=
    fix go {P} t1 t2 {struct t1} :=
      gmap_dep_ne_case t1 $ λ ml1 mx1 mr1,
        gmap_dep_ne_case t2 $ λ ml2 mx2 mr2,
          GNode (gmap_merge_aux go f ml1 ml2) (diag_None' f mx1 mx2)
                (gmap_merge_aux go f mr1 mr2).
  Local Definition gmap_dep_merge {A B C P} (f : option A → option B → option C) :
      gmap_dep A P → gmap_dep B P → gmap_dep C P :=
    gmap_merge_aux (gmap_dep_ne_merge f) f.
  Global Instance gmap_merge : Merge (gmap) :=
    λ {A B C} f '(GMap mt1) '(GMap mt2), GMap $ gmap_dep_merge f mt1 mt2.

  Local Definition gmap_fold_aux {A B P}
      (go : positive → B → gmap_dep_ne A P → B)
      (i : positive) (y : B) (mt : gmap_dep A P) : B :=
    match mt with GEmpty => y | GNodes t => go i y t end.
  Local Definition gmap_dep_ne_fold {A B} (f : positive → A → B → B) :
      ∀ {P}, positive → B → gmap_dep_ne A P → B :=
    fix go {P} i y t :=
      gmap_dep_ne_case t $ λ ml mx mr,
        gmap_fold_aux go i~1
          (gmap_fold_aux go i~0
            match mx with None => y | Some (p,x) => f (Pos.reverse i) x y end ml) mr.
  Local Definition gmap_dep_fold {A B P} (f : positive → A → B → B) :
      positive → B → gmap_dep A P → B :=
    gmap_fold_aux (gmap_dep_ne_fold f).
  Global Instance gmap_fold {A} :
      MapFold K A (gmap A) := λ {B} f y '(GMap mt),
    gmap_dep_fold (λ i x, match decode i with Some k => f k x | None => id end) 1 y mt.

  (** Proofs *)
  Local Definition GNode_valid {A P}
      (ml : gmap_dep A P~0) (mx : option (P 1 * A)) (mr : gmap_dep A P~1) :=
    match ml, mx, mr with GEmpty, None, GEmpty => False | _, _, _ => True end.
  Local Lemma gmap_dep_ind A (Q : ∀ P, gmap_dep A P → Prop) :
    (∀ P, Q P GEmpty) →
    (∀ P ml mx mr, GNode_valid ml mx mr → Q _ ml → Q _ mr → Q P (GNode ml mx mr)) →
    ∀ P mt, Q P mt.
  Proof.
    intros Hemp Hnode P [|t]; [done|]. induction t.
    - by apply (Hnode _ GEmpty None (GNodes _)).
    - by apply (Hnode _ GEmpty (Some (_,_)) GEmpty).
    - by apply (Hnode _ GEmpty (Some (_,_)) (GNodes _)).
    - by apply (Hnode _ (GNodes _) None GEmpty).
    - by apply (Hnode _ (GNodes _) None (GNodes _)).
    - by apply (Hnode _ (GNodes _) (Some (_,_)) GEmpty).
    - by apply (Hnode _ (GNodes _) (Some (_,_)) (GNodes _)).
  Qed.

  Local Lemma gmap_dep_lookup_GNode {A P} (ml : gmap_dep A P~0) mr mx i :
    gmap_dep_lookup i (GNode ml mx mr) =
      match i with
      | 1 => snd <$> mx | i~0 => gmap_dep_lookup i ml | i~1 => gmap_dep_lookup i mr
      end.
  Proof. by destruct ml, mx as [[]|], mr, i. Qed.

  Local Lemma gmap_dep_ne_lookup_not_None {A P} (t : gmap_dep_ne A P) :
    ∃ i, P i ∧ gmap_dep_ne_lookup i t ≠ None.
  Proof.
    induction t; repeat select (∃ _, _) (fun H => destruct H);
      try first [by eexists 1|by eexists _~0|by eexists _~1].
  Qed.
  Local Lemma gmap_dep_eq_empty {A P} (mt : gmap_dep A P) :
    (∀ i, P i → gmap_dep_lookup i mt = None) → mt = GEmpty.
  Proof.
    intros Hlookup. destruct mt as [|t]; [done|].
    destruct (gmap_dep_ne_lookup_not_None t); naive_solver.
  Qed.
  Local Lemma gmap_dep_eq {A P} (mt1 mt2 : gmap_dep A P) :
    (∀ i, ProofIrrel (P i)) →
    (∀ i, P i → gmap_dep_lookup i mt1 = gmap_dep_lookup i mt2) → mt1 = mt2.
  Proof.
    revert mt2. induction mt1 as [|P ml1 mx1 mr1 _ IHl IHr] using gmap_dep_ind;
      intros mt2 ? Hlookup;
      destruct mt2 as [|? ml2 mx2 mr2 _ _ _] using gmap_dep_ind.
    - done.
    - symmetry. apply gmap_dep_eq_empty. naive_solver.
    - apply gmap_dep_eq_empty. naive_solver.
    - f_equal.
      + apply (IHl _ _). intros i. generalize (Hlookup (i~0)).
        by rewrite !gmap_dep_lookup_GNode.
      + generalize (Hlookup 1). rewrite !gmap_dep_lookup_GNode.
        destruct mx1 as [[]|], mx2 as [[]|]; intros; simplify_eq/=;
          repeat f_equal; try  apply proof_irrel; naive_solver.
      + apply (IHr _ _). intros i. generalize (Hlookup (i~1)).
        by rewrite !gmap_dep_lookup_GNode.
  Qed.

  Local Lemma gmap_dep_ne_lookup_singleton {A P} i (p : P i) (x : A) :
    gmap_dep_ne_lookup i (gmap_dep_ne_singleton i p x) = Some x.
  Proof. revert P p. induction i; by simpl. Qed.
  Local Lemma gmap_dep_ne_lookup_singleton_ne {A P} i j (p : P i) (x : A) :
    i ≠ j → gmap_dep_ne_lookup j (gmap_dep_ne_singleton i p x) = None.
  Proof. revert P j p. induction i; intros ? [?|?|]; naive_solver. Qed.

  Local Lemma gmap_dep_partial_alter_GNode {A P} (f : option A → option A)
      i (p : P i) (ml : gmap_dep A P~0) mx mr :
    GNode_valid ml mx mr →
    gmap_dep_partial_alter f i p (GNode ml mx mr) =
      match i with
      | 1 => λ p, GNode ml ((p,.) <$> f (snd <$> mx)) mr
      | i~0 => λ p, GNode (gmap_dep_partial_alter f i p ml) mx mr
      | i~1 => λ p, GNode ml mx (gmap_dep_partial_alter f i p mr)
      end p.
  Proof. by destruct ml, mx as [[]|], mr. Qed.
  Local Lemma gmap_dep_lookup_partial_alter {A P} (f : option A → option A)
      (mt : gmap_dep A P) i (p : P i) :
    gmap_dep_lookup i (gmap_dep_partial_alter f i p mt) = f (gmap_dep_lookup i mt).
  Proof.
    revert i p. induction mt using gmap_dep_ind.
    { intros i p; simpl. destruct (f None); simpl; [|done].
      by rewrite gmap_dep_ne_lookup_singleton. }
    intros [] ?;
      rewrite ->gmap_dep_partial_alter_GNode, !gmap_dep_lookup_GNode by done;
      done || by destruct (f _).
  Qed.
  Local Lemma gmap_dep_lookup_partial_alter_ne {A P} (f : option A → option A)
      (mt : gmap_dep A P) i (p : P i) j :
    i ≠ j →
    gmap_dep_lookup j (gmap_dep_partial_alter f i p mt) = gmap_dep_lookup j mt.
  Proof.
    revert i p j; induction mt using gmap_dep_ind.
    { intros i p j ?; simpl. destruct (f None); simpl; [|done].
      by rewrite gmap_dep_ne_lookup_singleton_ne. }
    intros [] ? [] ?;
      rewrite ->gmap_dep_partial_alter_GNode, !gmap_dep_lookup_GNode by done;
      auto with lia.
  Qed.

  Local Lemma gmap_dep_lookup_fmap {A B P} (f : A → B) (mt : gmap_dep A P) i :
    gmap_dep_lookup i (gmap_dep_fmap f mt) = f <$> gmap_dep_lookup i mt.
  Proof.
    destruct mt as [|t]; simpl; [done|].
    revert i. induction t; intros []; by simpl.
  Qed.

  Local Lemma gmap_dep_omap_GNode {A B P} (f : A → option B)
      (ml : gmap_dep A P~0) mx mr :
    GNode_valid ml mx mr →
    gmap_dep_omap f (GNode ml mx mr) =
      GNode (gmap_dep_omap f ml) ('(p,x) ← mx; (p,.) <$> f x) (gmap_dep_omap f mr).
  Proof. by destruct ml, mx as [[]|], mr. Qed.
  Local Lemma gmap_dep_lookup_omap {A B P} (f : A → option B) (mt : gmap_dep A P) i :
    gmap_dep_lookup i (gmap_dep_omap f mt) = gmap_dep_lookup i mt ≫= f.
  Proof.
    revert i. induction mt using gmap_dep_ind; [done|].
    intros [];
      rewrite ->gmap_dep_omap_GNode, !gmap_dep_lookup_GNode by done; [done..|].
    destruct select (option _) as [[]|]; simpl; by try destruct (f _).
  Qed.

  Section gmap_merge.
    Context {A B C} (f : option A → option B → option C).

    Local Lemma gmap_dep_merge_GNode_GEmpty {P} (ml : gmap_dep A P~0) mx mr :
      GNode_valid ml mx mr →
      gmap_dep_merge f (GNode ml mx mr) GEmpty =
        GNode (gmap_dep_omap (λ x, f (Some x) None) ml) (diag_None' f mx None)
              (gmap_dep_omap (λ x, f (Some x) None) mr).
    Proof. by destruct ml, mx as [[]|], mr. Qed.
    Local Lemma gmap_dep_merge_GEmpty_GNode {P} (ml : gmap_dep B P~0) mx mr :
      GNode_valid ml mx mr →
      gmap_dep_merge f GEmpty (GNode ml mx mr) =
        GNode (gmap_dep_omap (λ x, f None (Some x)) ml) (diag_None' f None mx)
              (gmap_dep_omap (λ x, f None (Some x)) mr).
    Proof. by destruct ml, mx as [[]|], mr. Qed.
    Local Lemma gmap_dep_merge_GNode_GNode {P}
        (ml1 : gmap_dep A P~0) ml2 mx1 mx2 mr1 mr2 :
      GNode_valid ml1 mx1 mr1 → GNode_valid ml2 mx2 mr2 →
      gmap_dep_merge f (GNode ml1 mx1 mr1) (GNode ml2 mx2 mr2) =
        GNode (gmap_dep_merge f ml1 ml2) (diag_None' f mx1 mx2)
              (gmap_dep_merge f mr1 mr2).
    Proof. by destruct ml1, mx1 as [[]|], mr1, ml2, mx2 as [[]|], mr2. Qed.

    Local Lemma gmap_dep_lookup_merge {P} (mt1 : gmap_dep A P) (mt2 : gmap_dep B P) i :
      gmap_dep_lookup i (gmap_dep_merge f mt1 mt2) =
        diag_None f (gmap_dep_lookup i mt1) (gmap_dep_lookup i mt2).
    Proof.
      revert mt2 i; induction mt1 using gmap_dep_ind; intros mt2 i.
      { induction mt2 using gmap_dep_ind; [done|].
        rewrite ->gmap_dep_merge_GEmpty_GNode, gmap_dep_lookup_GNode by done.
        destruct i as [i|i|];
          rewrite ->?gmap_dep_lookup_omap, gmap_dep_lookup_GNode; simpl;
          [by destruct (gmap_dep_lookup i _)..|].
        destruct select (option _) as [[]|]; simpl; by try destruct (f _). }
      destruct mt2 using gmap_dep_ind.
      { rewrite ->gmap_dep_merge_GNode_GEmpty, gmap_dep_lookup_GNode by done.
        destruct i as [i|i|];
          rewrite ->?gmap_dep_lookup_omap, gmap_dep_lookup_GNode; simpl;
          [by destruct (gmap_dep_lookup i _)..|].
        destruct select (option _) as [[]|]; simpl; by try destruct (f _). }
      rewrite ->gmap_dep_merge_GNode_GNode by done.
      destruct i; rewrite ?gmap_dep_lookup_GNode; [done..|].
      repeat destruct select (option _) as [[]|]; simpl; by try destruct (f _).
    Qed.
  End gmap_merge.

  Section gmap_fold.
    Context {A B} (f : positive → A → B → B).

    Local Lemma gmap_dep_fold_GNode {P} i y (ml : gmap_dep A P~0) mx mr :
      GNode_valid ml mx mr →
      gmap_dep_fold f i y (GNode ml mx mr) = gmap_dep_fold f i~1
        (gmap_dep_fold f i~0
          match mx with None => y | Some (_,x) => f (Pos.reverse i) x y end ml) mr.
    Proof. by destruct ml, mx as [[]|], mr. Qed.

    Local Lemma gmap_dep_fold_ind {P} (Q : B → gmap_dep A P → Prop) (b : B) j :
      Q b GEmpty →
      (∀ i p x mt r, gmap_dep_lookup i mt = None →
        Q r mt →
        Q (f (Pos.reverse_go i j) x r) (gmap_dep_partial_alter (λ _, Some x) i p mt)) →
      ∀ mt, Q (gmap_dep_fold f j b mt) mt.
    Proof.
      intros Hemp Hinsert mt. revert Q b j Hemp Hinsert.
      induction mt as [|P ml mx mr ? IHl IHr] using gmap_dep_ind;
        intros Q b j Hemp Hinsert; [done|].
      rewrite ->gmap_dep_fold_GNode by done.
      apply (IHr (λ y mt, Q y (GNode ml mx mt))).
      { apply (IHl (λ y mt, Q y (GNode mt mx GEmpty))).
        { destruct mx as [[p x]|]; [|done].
          replace (GNode GEmpty (Some (p,x)) GEmpty) with
            (gmap_dep_partial_alter (λ _, Some x) 1 p GEmpty) by done.
          by apply Hinsert. }
        intros i p x mt r ??.
        replace (GNode (gmap_dep_partial_alter (λ _, Some x) i p mt) mx GEmpty)
          with (gmap_dep_partial_alter (λ _, Some x) (i~0) p (GNode mt mx GEmpty))
          by (by destruct mt, mx as [[]|]).
        apply Hinsert; by rewrite ?gmap_dep_lookup_GNode. }
      intros i p x mt r ??.
      replace (GNode ml mx (gmap_dep_partial_alter (λ _, Some x) i p mt))
        with (gmap_dep_partial_alter (λ _, Some x) (i~1) p (GNode ml mx mt))
        by (by destruct ml, mx as [[]|], mt).
      apply Hinsert; by rewrite ?gmap_dep_lookup_GNode.
    Qed.
  End gmap_fold.

  (** Instance of the finite map type class *)
  Global Instance gmap_finmap : FinMap K (gmap).
  Proof.
    split.
    - intros A [mt1] [mt2] Hlookup. f_equal. apply (gmap_dep_eq _ _ _).
      intros i [Hk]. destruct (decode i) as [k|]; simplify_eq/=. apply Hlookup.
    - done.
    - intros A f [mt] i. apply gmap_dep_lookup_partial_alter.
    - intros A f [mt] i j ?. apply gmap_dep_lookup_partial_alter_ne. naive_solver.
    - intros A b f [mt] i. apply gmap_dep_lookup_fmap.
    - intros A B f [mt] i. apply gmap_dep_lookup_omap.
    - intros A B C f [mt1] [mt2] i. apply gmap_dep_lookup_merge.
    - intros A B P f b Hemp Hinsert [mt].
      apply (gmap_dep_fold_ind _ (λ r mt, P r (GMap mt))); clear mt; [done|].
      intros i [Hk] x mt r ??; simpl. destruct (fmap_Some_1 _ _ _ Hk) as (k&->&->).
      assert (GMapKey Hk = gmap_key_encode k) as -> by (apply proof_irrel).
      by apply (Hinsert _ _ (GMap mt)).
  Qed.

  Global Program Instance gmap_countable
      `{Countable A} : Countable (gmap A) := {
    encode m := encode (map_to_list m : list (K * A));
    decode p := list_to_map <$> decode p
  }.
  Next Obligation.
    intros A ?? m; simpl. rewrite decode_encode; simpl.
    by rewrite list_to_map_to_list.
  Qed.

  (** Conversion to/from [Pmap] *)
  Local Definition gmap_dep_ne_to_pmap_ne {A} : ∀ {P}, gmap_dep_ne A P → Pmap_ne A :=
    fix go {P} t :=
      match t with
      | GNode001 r => PNode001 (go r)
      | GNode010 _ x => PNode010 x
      | GNode011 _ x r => PNode011 x (go r)
      | GNode100 l => PNode100 (go l)
      | GNode101 l r => PNode101 (go l) (go r)
      | GNode110 l _ x => PNode110 (go l) x
      | GNode111 l _ x r => PNode111 (go l) x (go r)
      end.
  Local Definition gmap_dep_to_pmap {A P} (mt : gmap_dep A P) : Pmap A :=
    match mt with
    | GEmpty => PEmpty
    | GNodes t => PNodes (gmap_dep_ne_to_pmap_ne t)
    end.
End GMap.

Require Import bedrock.prelude.bytestring.

Module BSCount <: COUNTABLE.
  Definition K := bs.
  Definition eq_dec : EqDecision K := _.
  Definition countable : Countable K := _.
End BSCount.

Module BSMap := GMap BSCount.

Notation bs_map := BSMap.gmap.
