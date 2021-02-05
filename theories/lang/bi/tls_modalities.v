(*
 * Copyright (C) BedRock Systems Inc. 2020
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
From iris.bi Require Import bi monpred.
From iris.proofmode Require Import tactics.

Require Import bedrock.lang.bi.mlens.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Bind Scope bi_scope with monPred.

Section Bi.
  Context {I J : biIndex} {PROP : bi}.
  Notation monPred := (monPred I PROP).
  Implicit Type (P Q : monPred) (L : MLens I J).

  (* @(L,j) P *)
  Program Definition monPred_exactly_at_def L (j : J) P :=
    MonPred (λ i, P ((L .= j) i)) _.
  Next Obligation. intros ?? P ???. rewrite mlens_set_mono; eauto. Qed.
  Local Definition monPred_exactly_at_aux : seal (@monPred_exactly_at_def).
  Proof. by eexists. Qed.
  Definition monPred_exactly_at := monPred_exactly_at_aux.(unseal).
  Definition monPred_exactly_at_eq :
    @monPred_exactly_at = @monPred_exactly_at_def
    := monPred_exactly_at_aux.(seal_eq).

  (* <obj>_{L} P *)
  Definition monPred_objectively_with L P : monPred :=
    (∀ j : J, monPred_exactly_at L j P).

  Program Definition monPred2_embed_def L (P : monpred.monPred J PROP) : monPred :=
    MonPred (λ i, P (i.^L)) _.
  Next Obligation. intros ? P ???. rewrite mlens_get_mono; eauto. Qed.
  Local Definition monPred2_embed_aux : seal (@monPred2_embed_def).
  Proof. by eexists. Qed.
  Definition monPred2_embed := monPred2_embed_aux.(unseal).
  Definition monPred2_embed_eq :
    @monPred2_embed = @monPred2_embed_def := monPred2_embed_aux.(seal_eq).

  Definition monPred_atleast L (j : J) : monPred :=
    monPred2_embed L (monPred_in j).
End Bi.

Arguments monPred_exactly_at {_ _ _} _ _ _%I.
Instance : Params (@monPred_exactly_at) 4 := {}.
Arguments monPred_objectively_with {_ _ _} _ _%I.
Instance : Params (@monPred_objectively_with) 3 := {}.
Arguments monPred2_embed {_ _ _} _ _%I.
Instance : Params (@monPred2_embed) 3 := {}.
Arguments monPred_atleast {_ _ _} _ _.


(* TODO: L should be TC-searched using the type I and J *)
(** @j P
    <obj>_J P *)
Notation "'@(' L , j ')' P" := (monPred_exactly_at L j P)
  (at level 50, format "@( L , j )  P") : bi_scope.
Notation "'<obj>_{' L '}' P" := (monPred_objectively_with L P)
  (at level 49, format "<obj>_{ L }  P"): bi_scope.
Notation "'||' P '||_{' L '}'" := (monPred2_embed L P)
  (at level 48, format "||  P  ||_{ L }"): bi_scope.
Notation "'⊒{' L '}' j" := (monPred_atleast L j)
  (at level 48, format "⊒{ L }  j"): bi_scope.

(* ObjectiveWith respect to J *)
Class ObjectiveWith {I J} {PROP: bi} (L: MLens I J) (P: monPred I PROP) :=
  objective_with i j : P i -∗ P ((L .= j) i).
Arguments ObjectiveWith {_ _ _} _ _%I.
Arguments objective_with {_ _ _} _ _%I {_}.
#[global] Hint Mode ObjectiveWith ! ! + + ! : typeclass_instances.
Instance: Params (@ObjectiveWith) 3 := {}.


(* LocalWith respect to J *)
(* This means that P only depends on the component J, anything else can be
  arbitrary. *)
Class LocalWith {I J} {PROP: bi} (L: MLens I J) (P: monPred I PROP) :=
  local_with i1 i2 (Eq: i1.^L = i2.^L): P i1 -∗ P i2.
Arguments LocalWith {_ _ _} _ _%I.
Arguments local_with {_ _ _} _ _%I {_}.
#[global] Hint Mode LocalWith ! ! + + ! : typeclass_instances.
Instance: Params (@LocalWith) 3 := {}.

Local Ltac unfold_at :=
  constructor => i;
    rewrite /= /monPred_objectively_with /monPred_atleast
            ?monPred_exactly_at_eq ?monPred2_embed_eq /=.

Section MLid_properties.
  Context {I : biIndex} {PROP : bi}.
  Implicit Types (P : monPred I PROP).

  Lemma monPred_objectively_with_id_objectively P :
    <obj> P ⊣⊢ <obj>_{MLid} P.
  Proof. unfold_at. by rewrite monPred_at_forall /= monPred_at_objectively. Qed.

  Lemma objective_with_id_objective P :
    Objective P <-> ObjectiveWith MLid P.
  Proof. done. Qed.

  Global Instance objective_with_id_objective_1 P
    `{!ObjectiveWith MLid P}: Objective P.
  Proof. intros. by apply objective_with_id_objective. Qed.
End MLid_properties.

(** monPred_exactly_at **)

Section exactlyAt.
Context {I J : biIndex} {PROP : bi}.
Notation monPred := (monPred I PROP).
Implicit Type (P Q : monPred) (L : MLens I J).

Global Instance monPred_exactly_at_mono L :
  Proper ((⊑) ==> (⊢) ==> (⊢)) (monPred_exactly_at (PROP:=PROP) L).
Proof.
  intros i1 i2 Lei P Q EN. unfold_at.
  rewrite EN mlens_set_mono; eauto.
Qed.
Global Instance monPred_exactly_at_flip_mono L :
  Proper (flip (⊑) ==> flip (⊢) ==> flip (⊢)) (monPred_exactly_at (PROP:=PROP) L).
Proof. intros i1 i2 Lei P Q EN. simpl in *. by rewrite Lei EN. Qed.
Global Instance monPred_exactly_at_proper L j :
  Proper ((≡) ==> (≡)) (monPred_exactly_at (PROP:=PROP) L j).
Proof.
  intros P Q EQ. apply bi.equiv_spec.
  by split; apply monPred_exactly_at_mono; auto; rewrite EQ.
Qed.

Lemma monPred_exactly_at_elim_objectively_with L j P :
  @(L,j) <obj>_{L} P ⊣⊢ <obj>_{L} P.
Proof.
  unfold_at. rewrite !monPred_at_forall /=.
  setoid_rewrite mlens_set_set. eauto.
Qed.

Lemma monPred_objectively_with_into_exactly_at L j P :
  <obj>_{L} P ⊢ @(L,j) P.
Proof. unfold_at. rewrite monPred_at_forall /=. eauto. Qed.

Corollary monPred_exactly_at_objectively_with_elim L j P :
  @(L,j) <obj>_{L} P ⊢ @(L,j) P.
Proof.
  etrans; last apply monPred_objectively_with_into_exactly_at.
  by rewrite monPred_exactly_at_elim_objectively_with.
Qed.

Lemma objective_with_intro_exactly_at L P `{!ObjectiveWith L P} j :
  P ⊣⊢ @(L,j) P.
Proof.
  unfold_at. iSplit.
  - rewrite -objective_with. eauto.
  - iIntros "P". rewrite (objective_with L P ((L .= j) i) (i.^L)).
    by rewrite mlens_set_set mlens_set_get.
Qed.

Global Instance monPred_exactly_at_objective_with L P j :
  ObjectiveWith L (@(L,j) P).
Proof. intros i j'. by rewrite monPred_exactly_at_eq /= mlens_set_set. Qed.

End exactlyAt.

Lemma monPred_exactly_at_objective_with_lens {I J K PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP) k :
  Lj .<= Lk -> ObjectiveWith Lj (@(Lk,k) P).
Proof. intros Le ??. by rewrite monPred_exactly_at_eq /= mlens_le_set_outer. Qed.

Lemma monPred_exactly_at_objective_with_disjoint {I J K PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP) k
  `{OBJ : !ObjectiveWith Lj P} :
  Lj .## Lk -> ObjectiveWith Lj (@(Lk,k) P).
Proof. intros DISJ ??. by rewrite monPred_exactly_at_eq /= DISJ -objective_with. Qed.


(** ObjectiveWith *)
Instance objective_with_proper {I J} {PROP} :
  Proper ((.==) ==> equiv ==> iff) (@ObjectiveWith I J PROP).
Proof.
  intros L1 L2 LeL P Q LeP. split; intros OBJ i j.
  - by rewrite -LeP -LeL -objective_with.
  - by rewrite LeP LeL -objective_with.
Qed.

(* Can't state as a Proper instance *)
Lemma objective_with_lens_mono {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP)
  `{!ObjectiveWith Lk P} :
  Lj .<= Lk -> ObjectiveWith Lj P.
Proof. intros Le i j. by rewrite -(mlens_le_set_inner _ Lk) //. Qed.
(* But we can state a weaker one with J = K *)
Instance objective_with_lens_mono' {I J} {PROP} :
  Proper (flip (.<=) ==> equiv ==> impl) (@ObjectiveWith I J PROP).
Proof. intros ??? ?? <- ?. eapply objective_with_lens_mono; eauto. Qed.
Instance objective_with_lens_flip_mono' {I J} {PROP} :
  Proper ((.<=) ==> equiv ==> flip (impl)) (@ObjectiveWith I J PROP).
Proof. intros ??? ?? <- ?. eapply objective_with_lens_mono; eauto. Qed.

Lemma objective_with_lens_equiv {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP) :
  Lj .≡ Lk ->
  ObjectiveWith Lj P <-> ObjectiveWith Lk P.
Proof. intros []. split; intros; eapply objective_with_lens_mono; eauto. Qed.
(* Weaker instance with J = K *)
Instance objective_with_lens_equiv' {I J} {PROP} :
  Proper ((.≡) ==> equiv ==> iff) (@ObjectiveWith I J PROP).
Proof. intros ?? [??] ?? ->. split; eapply objective_with_lens_mono'; eauto. Qed.

(** monPred_objectively_with *)

Section objectivelyWith.
  Context {I J : biIndex} {PROP : bi}.
  Notation monPred := (monPred I PROP).
  Implicit Type (P Q : monPred) (L : MLens I J).

  Global Instance monPred_objectively_with_objective_with L P :
    ObjectiveWith L (<obj>_{L} P).
  Proof.
    intros i j. rewrite !monPred_at_forall monPred_exactly_at_eq /=.
    by setoid_rewrite mlens_set_set.
  Qed.

  Lemma monPred_objectively_with_elim L P :
    <obj>_{L} P ⊢ P.
  Proof.
    unfold_at. rewrite monPred_at_forall /= -{2}(mlens_set_get L i).
    by eauto.
  Qed.

  Lemma objective_with_intro_objectively_with L P `{!ObjectiveWith L P} :
    P ⊣⊢ <obj>_{L} P.
  Proof.
    unfold_at. rewrite monPred_at_forall /=. iSplit.
    - iIntros "P" (x). by rewrite -objective_with.
    - iIntros "P". rewrite -{2}(mlens_set_get L i). by iApply "P".
  Qed.

  (* Lemma monPred_objectively_commute
    <obj>_{L1} <obj>_{L2} P ⊣⊢ <obj>_{L2} <obj>_{L1} P *)
End objectivelyWith.

Section objectivelyWith_lens.
  Context {I J K : biIndex} {PROP : bi}.
  Implicit Types (Lj : MLens I J) (Lk : MLens I K) (P: monPred I PROP).

  Lemma monPred_objectively_with_lens_mono Lj Lk P :
    Lj .<= Lk ->
    <obj>_{Lk} P ⊢ <obj>_{Lj} P.
  Proof.
    intros Le. unfold_at. rewrite !monPred_at_forall /=.
    apply bi.forall_intro=> x.
    by rewrite (bi.forall_elim (((Lj .= x) i).^Lk)) mlens_le_set_inner //.
  Qed.

  Corollary monPred_objectively_with_objective_with_lens_mono Lj Lk P :
    Lj .<= Lk -> ObjectiveWith Lj (<obj>_{Lk} P).
  Proof.
    intros.
    eapply objective_with_lens_mono; eauto.
    by apply monPred_objectively_with_objective_with.
  Qed.

  Corollary objective_with_intro_objectively_with_lens_mono Lj Lk P
    `{!ObjectiveWith Lk P} :
    Lj .<= Lk -> P ⊢ <obj>_{Lj} P.
  Proof.
    intros. erewrite (objective_with_intro_objectively_with Lj) at 1; eauto.
    eapply objective_with_lens_mono; eauto.
  Qed.
End objectivelyWith_lens.

Lemma monPred_objectively_with_lens_equiv {I J K} {PROP}
  (Lj : MLens I J) (Lk : MLens I K) (P : monPred I PROP) :
  Lj .≡ Lk -> <obj>_{Lj} P ⊣⊢ <obj>_{Lk} P.
Proof.
  intros []. apply bi.equiv_spec.
  by split; apply monPred_objectively_with_lens_mono.
Qed.

(* Weaker instances with J = K *)
Instance monPred_objectively_with_lens_mono' {I J} {PROP} :
  Proper (flip (.<=) ==> (⊢) ==> (⊢)) (@monPred_objectively_with I J PROP).
Proof.
  intros L1 L2 LeL P Q Le. rewrite monPred_objectively_with_lens_mono; eauto.
  simpl in *. solve_proper.
Qed.
Instance monPred_objectively_with_lens_flip_mono' {I J} {PROP} :
  Proper ((.<=) ==> flip (⊢) ==> flip (⊢)) (@monPred_objectively_with I J PROP).
Proof. intros ??? P Q. by apply monPred_objectively_with_lens_mono'. Qed.

Instance monPred_objectively_with_mono {I J PROP} :
  Proper ((.≡) ==> (⊢) ==> (⊢)) (@monPred_objectively_with I J PROP).
Proof. intros ?? [Eq1 Eq2] P Q PQ. solve_proper. Qed.
Instance monPred_objectively_with_flip_mono {I J PROP} :
  Proper ((.≡) ==> flip (⊢) ==> flip (⊢)) (@monPred_objectively_with I J PROP).
Proof. intros ??? ??. by apply monPred_objectively_with_mono. Qed.

Instance monPred_objectively_with_lens_equiv_proper {I J} {PROP} :
  Proper ((.≡) ==> (⊣⊢) ==> (⊣⊢)) (@monPred_objectively_with I J PROP).
Proof.
  intros ??[] ?? [Eq1 Eq2]%bi.equiv_spec.
  apply bi.equiv_spec. split; by apply monPred_objectively_with_lens_mono'.
Qed.
Instance monPred_objectively_with_lens_eq_proper {I J} {PROP} :
  Proper ((.==) ==> (⊣⊢) ==> (⊣⊢)) (@monPred_objectively_with I J PROP).
Proof. intros ?? ?%is_subrelation. solve_proper. Qed.

Instance monPred_objectively_with_eq_mono {I J PROP} :
  Proper ((.==) ==> (⊢) ==> (⊢)) (@monPred_objectively_with I J PROP).
Proof. intros ?? ?%is_subrelation. solve_proper. Qed.
Instance monPred_objectively_with_eq_flip_mono {I J PROP} :
  Proper ((.==) ==> flip (⊢) ==> flip (⊢)) (@monPred_objectively_with I J PROP).
Proof. intros ??? ??. by apply monPred_objectively_with_eq_mono. Qed.

(* TODO: many other weaker instances for monPred2_embed with J = K *)
Section monPred2_embed.
  Context {I J : biIndex} {PROP : bi}.
  Notation monPred := (monPred I PROP).
  Implicit Type (P Q : monPred) (L : MLens I J).

  Global Instance monPred2_embed_mono L :
    Proper ((⊢) ==> (⊢)) (monPred2_embed (PROP:=PROP) L).
  Proof. intros P Q Eq. unfold_at. solve_proper. Qed.
  Global Instance monPred2_embed_proper L :
    Proper ((≡) ==> (≡)) (monPred2_embed (PROP:=PROP) L).
  Proof.
    intros P Q Eq. apply bi.equiv_spec.
    by split; apply monPred2_embed_mono; rewrite Eq.
  Qed.

  Global Instance monPred_atleast_mono L :
    Proper (flip (⊑) ==> (⊢)) (monPred_atleast (PROP:=PROP) L).
  Proof. intros ?? Lei. unfold_at. by rewrite Lei. Qed.
End monPred2_embed.

Section mlens_prod.
  Context {I J K : biIndex} {PROP : bi}.
  Implicit Types (L : MLens I (J *i K))
                 (P : monPred I PROP) (Lj : MLens I J) (Lk : MLens I K).

  Lemma monPred_exactly_at_objective_with_disjoint_left Lj Lk P j
    `{!ObjectiveWith Lk P}
    (D: Lj .## Lk) :
    ObjectiveWith (Lj .+_{D} Lk) (@(Lj, j) P).
  Proof.
    intros jk1 jk2.
    by rewrite monPred_exactly_at_eq /= D mlens_set_set -D -objective_with.
  Qed.

  Lemma monPred_exactly_at_objective_with_disjoint_right Lj Lk P j
    `{!ObjectiveWith Lk P}
    (D: Lk .## Lj) :
    ObjectiveWith (Lk .+_{D} Lj) (@(Lj, j) P).
  Proof.
    intros jk1 jk2.
    by rewrite monPred_exactly_at_eq /= mlens_set_set D -objective_with.
  Qed.

  Lemma monPred_objectively_with_objective_with_disjoint_left Lj Lk P
    `{!ObjectiveWith Lk P}
    (D: Lj .## Lk) :
    ObjectiveWith (Lj .+_{D} Lk) (<obj>_{Lj} P).
  Proof.
    intros i [j k]. rewrite !monPred_at_forall monPred_exactly_at_eq /=.
    setoid_rewrite D.
    setoid_rewrite mlens_set_set.
    setoid_rewrite <-D.
    setoid_rewrite <-(objective_with Lk _ _ k). eauto.
  Qed.

  Lemma monPred_objectively_with_objective_with_disjoint_right Lj Lk P
    `{!ObjectiveWith Lk P}
    (D: Lk .## Lj) :
    ObjectiveWith (Lk .+_{D} Lj) (<obj>_{Lj} P).
  Proof.
    intros i [k j]. rewrite !monPred_at_forall monPred_exactly_at_eq /=.
    setoid_rewrite mlens_set_set.
    setoid_rewrite D.
    setoid_rewrite <-(objective_with Lk _ _ k). eauto.
  Qed.

  Lemma objective_with_join Lj Lk P
    `{!ObjectiveWith Lj P, !ObjectiveWith Lk P}
    (D: Lj .## Lk) :
    ObjectiveWith (Lj .+_{D} Lk) P.
  Proof. intros i [j k]. by rewrite /= -!objective_with. Qed.
End mlens_prod.

Section bi_prod.
  Context {I J K : biIndex} {PROP : bi}.
  Implicit Types (L : MLens I (J *i K)) (P : monPred I PROP).

  Global Instance monPred_exactly_with_objective_with_left L P j
    `{!ObjectiveWith (L.r) P} :
    ObjectiveWith L (@(L.l, j) P).
  Proof.
    eapply objective_with_lens_equiv; last eapply
      monPred_exactly_at_objective_with_disjoint_left; last eauto.
    by apply is_subrelation, mlens_eq_split_join.
  Qed.

  Global Instance monPred_exactly_with_objective_with_right L P k
    `{!ObjectiveWith (L.l) P} :
    ObjectiveWith L (@(L.r, k) P).
  Proof.
    eapply objective_with_lens_equiv; last eapply
      monPred_exactly_at_objective_with_disjoint_right; last eauto.
    by apply is_subrelation, mlens_eq_split_join.
  Qed.

  Global Instance monPred_objectively_with_objective_with_left L P
    `{!ObjectiveWith (L.r) P} :
    ObjectiveWith L (<obj>_{L.l} P).
  Proof.
    eapply objective_with_lens_equiv; last eapply
      monPred_objectively_with_objective_with_disjoint_left; last eauto.
    by apply is_subrelation, mlens_eq_split_join.
  Qed.

  Global Instance monPred_objectively_with_objective_with_right L P
    `{!ObjectiveWith (L.l) P} :
    ObjectiveWith L (<obj>_{L.r} P).
  Proof.
    eapply objective_with_lens_equiv; last eapply
      monPred_objectively_with_objective_with_disjoint_right; last eauto.
    by apply is_subrelation, mlens_eq_split_join.
  Qed.

  Lemma objective_with_join_lr L P
    `{!ObjectiveWith (L.l) P, !ObjectiveWith (L.r) P} :
    ObjectiveWith L P.
  Proof.
    eapply objective_with_lens_equiv; last eapply
      objective_with_join.
    by apply is_subrelation, mlens_eq_split_join.
    eauto. eauto.
  Qed.

  Global Instance objective_with_split_l L P
    `{!ObjectiveWith L P} :
    ObjectiveWith (L.l) P.
  Proof. apply : (objective_with_lens_mono _ L). apply mlens_le_left. Qed.

  Global Instance objective_with_split_r L P
    `{!ObjectiveWith L P} :
    ObjectiveWith (L.r) P.
  Proof. apply : (objective_with_lens_mono _ L). apply mlens_le_right. Qed.

  Global Instance monPred2_embed_objective_with_left L (P : monPred K PROP) :
    ObjectiveWith (L.l) (|| P ||_{L.r}).
  Proof. intros i j. by rewrite monPred2_embed_eq /= mlens_get_set /=. Qed.

  Global Instance monPred2_embed_objective_with_right L (P : monPred J PROP) :
    ObjectiveWith (L.r) (|| P ||_{L.l}).
  Proof. intros i k. by rewrite monPred2_embed_eq /= mlens_get_set /=. Qed.

  Corollary monPred_atleast_objective_with_left L (k : K) :
    ObjectiveWith (PROP:=PROP) (L.l) (⊒{L.r} k).
  Proof. apply _. Qed.

  Corollary monPred_atleast_objective_with_right L (j : J) :
    ObjectiveWith (PROP:=PROP) (L.r) (⊒{L.l} j).
  Proof. apply _. Qed.
End bi_prod.

Section other_instances.
  Context {I J : biIndex} {PROP : bi}.
  Local Notation monPred := (monPred I PROP).
  Implicit Types (L : MLens I J) (P Q : monPred).

  Global Instance monPred_atleast_persistent L i0 :
    Persistent ((⊒{L} i0)%I : monPred).
  Proof. unfold_at. rewrite monPred_at_persistently /= monPred_at_in. eauto. Qed.
  Global Instance monPred_atleast_timeless L i0 :
    Timeless ((⊒{L} i0)%I : monPred).
  Proof.
    unfold_at. rewrite monPred_at_later /= monPred_at_except_0 /=!monPred_at_in.
    by iIntros ">$".
  Qed.

  Global Instance embed_objective_with L (P : PROP) : ObjectiveWith L ⎡P⎤.
  Proof. intros ??. by rewrite !monPred_at_embed. Qed.
  Global Instance pure_objective_with L φ : ObjectiveWith (PROP:=PROP) L ⌜φ⌝.
  Proof. intros ??. by rewrite !monPred_at_pure. Qed.
  Global Instance emp_objective_with L : @ObjectiveWith I J PROP L emp.
  Proof. intros ??. by rewrite !monPred_at_emp. Qed.

  Global Instance and_objective_with L P Q
    `{!ObjectiveWith L P, !ObjectiveWith L Q} : ObjectiveWith L (P ∧ Q).
  Proof. intros i j. by rewrite !monPred_at_and -!(objective_with L _ i). Qed.
  Global Instance or_objective L P Q
    `{!ObjectiveWith L P, !ObjectiveWith L Q} : ObjectiveWith L (P ∨ Q).
  Proof. intros i j. by rewrite !monPred_at_or !(objective_with L _ i). Qed.

  Global Instance impl_objective_with L P Q
    `{!ObjectiveWith L P, !ObjectiveWith L Q} : ObjectiveWith L (P → Q).
  Proof.
    intros i j.
    rewrite !monPred_at_impl. apply bi.forall_intro=> i'.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=>Le.
    assert (Le2 := mlens_set_reset_order _ _ _ _ Le).
    rewrite (bi.forall_elim ((L .= (i.^L)) i')) bi.pure_impl_forall bi.forall_elim //.
    rewrite (objective_with L Q _ (i'.^L)) mlens_set_set mlens_set_get.
    apply bi.impl_mono; eauto.
  Qed.

  Global Instance forall_objective_with {A} L (Φ : A → monPred)
    `{∀ x : A, ObjectiveWith L (Φ x)} :
    ObjectiveWith L (∀ x, Φ x).
  Proof.
    intros i j.
    rewrite !monPred_at_forall. by setoid_rewrite (objective_with L _ i).
  Qed.

  Global Instance exist_objective_with {A} L (Φ : A → monPred)
    `{∀ x : A, ObjectiveWith L (Φ x)} :
    ObjectiveWith L (∃ x, Φ x).
  Proof.
    intros i j.
    rewrite !monPred_at_exist. by setoid_rewrite (objective_with L _ i).
  Qed.

  Global Instance sep_objective_with L P Q
    `{OP: !ObjectiveWith L P, OQ: !ObjectiveWith L Q} :
    ObjectiveWith L (P ∗ Q)%I.
  Proof.  intros i j. by rewrite !monPred_at_sep !(objective_with L _ i). Qed.

  Global Instance wand_objective_with L P Q
    `{!ObjectiveWith L P, !ObjectiveWith L Q} : ObjectiveWith L (P -∗ Q).
  Proof.
    intros i j.
    rewrite !monPred_at_wand. apply bi.forall_intro=> i'.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=>Le.
    assert (Le2 := mlens_set_reset_order _ _ _ _ Le).
    rewrite (bi.forall_elim ((L .= (i.^L)) i')) bi.pure_impl_forall bi.forall_elim //.
    rewrite (objective_with L Q _ (i'.^L)) mlens_set_set mlens_set_get.
    apply bi.wand_mono; eauto.
  Qed.
  Global Instance persistently_objective_with L P
    `{!ObjectiveWith L P} : ObjectiveWith L (<pers> P).
  Proof.
    intros i j. by rewrite !monPred_at_persistently !(objective_with L _ i).
  Qed.

  Global Instance affinely_objective_with L P
    `{!ObjectiveWith L P} : ObjectiveWith L (<affine> P).
  Proof. rewrite /bi_affinely. apply _. Qed.
  Global Instance intuitionistically_objective_with L P
    `{!ObjectiveWith L P} : ObjectiveWith L (□ P).
  Proof. rewrite /bi_intuitionistically. apply _. Qed.
  Global Instance absorbingly_objective_with L P
    `{!ObjectiveWith L P} : ObjectiveWith L (<absorb> P).
  Proof. rewrite /bi_absorbingly. apply _. Qed.
  Global Instance persistently_if_objective_with L P p
    `{!ObjectiveWith L P} : ObjectiveWith L (<pers>?p P).
  Proof. rewrite /bi_persistently_if. destruct p; apply _. Qed.
  Global Instance affinely_if_objective_with L P p
    `{!ObjectiveWith L P} : ObjectiveWith L (<affine>?p P).
  Proof. rewrite /bi_affinely_if. destruct p; apply _. Qed.
  Global Instance absorbingly_if_objective_with L P p
    `{!ObjectiveWith L P} : ObjectiveWith L (<absorb>?p P).
  Proof. rewrite /bi_absorbingly_if. destruct p; apply _. Qed.
  Global Instance intuitionistically_if_objective_with L P p
    `{!ObjectiveWith L P} : ObjectiveWith L (□?p P).
  Proof. rewrite /bi_intuitionistically_if. destruct p; apply _. Qed.

  Global Instance bupd_objective_with `{BiBUpd PROP} L P
    `{!ObjectiveWith L P} : ObjectiveWith L (|==> P)%I.
  Proof. intros ??. by rewrite !monPred_at_bupd (objective_with L). Qed.

  Global Instance fupd_objective_with `{BiFUpd PROP} L E1 E2 P
    `{!ObjectiveWith L P} : ObjectiveWith L (|={E1,E2}=> P)%I.
  Proof. intros ??. by rewrite !monPred_at_fupd (objective_with L). Qed.

  Global Instance later_objective_with L P
    `{!ObjectiveWith L P} : ObjectiveWith L (▷ P).
  Proof. intros ??. by rewrite !monPred_at_later (objective_with L). Qed.
  Global Instance laterN_objective_with L P
    `{!ObjectiveWith L P} n : ObjectiveWith L (▷^n P).
  Proof. induction n; apply _. Qed.
  Global Instance except0_objective_with L P
    `{!ObjectiveWith L P} : ObjectiveWith L (◇ P).
  Proof. rewrite /bi_except_0. apply _. Qed.

  Global Instance plainly_objective_with `{BiPlainly PROP} L P :
    ObjectiveWith L (■ P).
  Proof. rewrite monPred_plainly_unfold. apply _. Qed.
  Global Instance plainly_if_objective_with `{BiPlainly PROP} L P p
    `{!ObjectiveWith L P} : ObjectiveWith L (■?p P).
  Proof. rewrite /plainly_if. destruct p; apply _. Qed.

  (* LocalWith *) (* TODO: more instances *)
  Global Instance embed_local_with L (P : PROP) : LocalWith L ⎡P⎤.
  Proof. intros ???. by rewrite !monPred_at_embed. Qed.
  Global Instance pure_local_with L φ : LocalWith (PROP:=PROP) L ⌜φ⌝.
  Proof. intros ???. by rewrite !monPred_at_pure. Qed.
  Global Instance emp_local_with L : @LocalWith I J PROP L emp.
  Proof. intros ???. by rewrite !monPred_at_emp. Qed.

  Global Instance and_local_with L P Q
    `{!LocalWith L P, !LocalWith L Q} : LocalWith L (P ∧ Q).
  Proof. intros i j Eq. by rewrite !monPred_at_and -!(local_with L _ i). Qed.
  Global Instance or_local_with L P Q
    `{!LocalWith L P, !LocalWith L Q} : LocalWith L (P ∨ Q).
  Proof. intros i j Eq. by rewrite !monPred_at_or !(local_with L _ i). Qed.

  Global Instance impl_local_with L P Q
    `{!LocalWith L P, !LocalWith L Q} : LocalWith L (P → Q).
  Proof.
    intros i j Eqi.
    rewrite !monPred_at_impl. apply bi.forall_intro=> i'.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=>Le.
    assert (Le' : i ⊑ (L .= i'.^L) i).
    { rewrite -{1}(mlens_set_get L i). apply mlens_set_mono; [|done].
      rewrite Eqi. by apply mlens_get_mono. }
    rewrite (bi.forall_elim ((L .= (i'.^L)) i)) bi.pure_impl_forall bi.forall_elim //.
    rewrite (local_with L Q _ i'); last by rewrite mlens_get_set.
    apply bi.impl_mono; eauto.
    by rewrite (local_with L) // mlens_get_set.
  Qed.

  Global Instance forall_local_with {A} L (Φ : A → monPred)
    `{∀ x : A, LocalWith L (Φ x)} :
    LocalWith L (∀ x, Φ x).
  Proof.
    intros i j ?.
    rewrite !monPred_at_forall. by setoid_rewrite (local_with L _ _ _ Eq).
  Qed.

  Global Instance exist_local_with {A} L (Φ : A → monPred)
    `{∀ x : A, LocalWith L (Φ x)} :
    LocalWith L (∃ x, Φ x).
  Proof.
    intros i j ?.
    rewrite !monPred_at_exist. by setoid_rewrite (local_with L _ _ _ Eq).
  Qed.

  Global Instance sep_local_with L P Q
    `{OP: !LocalWith L P, OQ: !LocalWith L Q} :
    LocalWith L (P ∗ Q)%I.
  Proof.  intros i j ?. by rewrite !monPred_at_sep !(local_with L _ i j). Qed.

  Global Instance wand_local_with L P Q
    `{!LocalWith L P, !LocalWith L Q} : LocalWith L (P -∗ Q).
  Proof.
    intros i j Eqi.
    rewrite !monPred_at_wand. apply bi.forall_intro=> i'.
    rewrite bi.pure_impl_forall. apply bi.forall_intro=>Le.
    assert (Le' : i ⊑ (L .= i'.^L) i).
    { rewrite -{1}(mlens_set_get L i). apply mlens_set_mono; [|done].
      rewrite Eqi. by apply mlens_get_mono. }
    rewrite (bi.forall_elim ((L .= (i'.^L)) i)) bi.pure_impl_forall bi.forall_elim //.
    rewrite (local_with L Q _ i'); last by rewrite mlens_get_set.
    apply bi.wand_mono; eauto.
    by rewrite (local_with L) // mlens_get_set.
  Qed.
  Global Instance persistently_local_with L P
    `{!LocalWith L P} : LocalWith L (<pers> P).
  Proof.
    intros i j ?. by rewrite !monPred_at_persistently !(local_with L _ i j).
  Qed.

  Global Instance affinely_local_with L P
    `{!LocalWith L P} : LocalWith L (<affine> P).
  Proof. rewrite /bi_affinely. apply _. Qed.
  Global Instance intuitionistically_local_with L P
    `{!LocalWith L P} : LocalWith L (□ P).
  Proof. rewrite /bi_intuitionistically. apply _. Qed.
  Global Instance absorbingly_local_with L P
    `{!LocalWith L P} : LocalWith L (<absorb> P).
  Proof. rewrite /bi_absorbingly. apply _. Qed.
  Global Instance persistently_if_local_with L P p
    `{!LocalWith L P} : LocalWith L (<pers>?p P).
  Proof. rewrite /bi_persistently_if. destruct p; apply _. Qed.
  Global Instance affinely_if_local_with L P p
    `{!LocalWith L P} : LocalWith L (<affine>?p P).
  Proof. rewrite /bi_affinely_if. destruct p; apply _. Qed.
  Global Instance absorbingly_if_local_with L P p
    `{!LocalWith L P} : LocalWith L (<absorb>?p P).
  Proof. rewrite /bi_absorbingly_if. destruct p; apply _. Qed.
  Global Instance intuitionistically_if_local_with L P p
    `{!LocalWith L P} : LocalWith L (□?p P).
  Proof. rewrite /bi_intuitionistically_if. destruct p; apply _. Qed.

  Global Instance bupd_local_with `{BiBUpd PROP} L P
    `{!LocalWith L P} : LocalWith L (|==> P)%I.
  Proof. intros i j ?. by rewrite !monPred_at_bupd (local_with L _ i j). Qed.

  Global Instance fupd_local_with `{BiFUpd PROP} L E1 E2 P
    `{!LocalWith L P} : LocalWith L (|={E1,E2}=> P)%I.
  Proof. intros i j ?. by rewrite !monPred_at_fupd (local_with L _ i j). Qed.

  Global Instance later_local_with L P
    `{!LocalWith L P} : LocalWith L (▷ P).
  Proof. intros i j ?. by rewrite !monPred_at_later (local_with L _ i j). Qed.
  Global Instance laterN_local_with L P
    `{!LocalWith L P} n : LocalWith L (▷^n P).
  Proof. induction n; apply _. Qed.
  Global Instance except0_local_with L P
    `{!LocalWith L P} : LocalWith L (◇ P).
  Proof. rewrite /bi_except_0. apply _. Qed.

  Global Instance plainly_local_with `{BiPlainly PROP} L P :
    LocalWith L (■ P).
  Proof. rewrite monPred_plainly_unfold. apply _. Qed.
  Global Instance plainly_if_local_with `{BiPlainly PROP} L P p
    `{!LocalWith L P} : LocalWith L (■?p P).
  Proof. rewrite /plainly_if. destruct p; apply _. Qed.

  (* TODO: big_op *)

End other_instances.

(* TODO: IPM instances *)
