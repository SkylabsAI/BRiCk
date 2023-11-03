(*
 * Copyright (c) 2020-22 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Theory of representation predicates [Rep].
For an introduction see
[fmdeps/cpp2v-core/theories/noimport/doc/cpp/howto_sequential.v]. *)

From iris.proofmode Require Import proofmode.
From bedrock.lang.bi Require Import fractional.

From bedrock.lang.bi Require Import prelude only_provable observe laterable.
From bedrock.lang.bi Require Export monpred.
(** ^^ Delicate; export canonical structure (CS) for [monPred].
Export order can affect CS inference. *)

From bedrock.lang.cpp Require Import semantics.values logic.mpred bi.cfractional.
From bedrock.lang.cpp Require Export logic.rep_defs.
(** ^^ Delicate; export canonical structure (CS) for [Rep].
Export order can affect CS inference. *)

Import ChargeNotation.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Implicit Types (σ resolve : genv) (p : ptr) (o : offset).
  Implicit Type (R : Rep).

  (* Keeps proofs simple with recent Iris. *)
  #[local] Existing Instance as_fractional_fractional.
  #[local] Hint Mode AsFractional - - - - : typeclass_instances.

  #[global] Instance as_Rep_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.
  #[global] Instance as_Rep_proper :
    Proper (pointwise_relation _ (≡) ==> (≡)) as_Rep.
  Proof. intros R1 R2 HR. constructor=>p. apply HR. Qed.

  #[global] Instance as_Rep_mono :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) as_Rep.
  Proof. by constructor. Qed.
  #[global] Instance as_Rep_flip_mono :
    Proper (pointwise_relation _ (flip (⊢)) ==> flip (⊢)) as_Rep.
  Proof. by constructor. Qed.

  #[global] Instance as_Rep_persistent P :
    (∀ p, Persistent (P p)) → Persistent (as_Rep P).
  Proof.
    intros HP. constructor=>p. by rewrite monPred_at_persistently -HP.
  Qed.
  #[global] Instance as_Rep_affine P :
    (∀ p, Affine (P p)) → Affine (as_Rep P) := _.
  #[global] Instance as_Rep_timeless P :
    (∀ p, Timeless (P p)) → Timeless (as_Rep P).
  Proof.
    intros HP. constructor=>p.
    by rewrite monPred_at_later monPred_at_except_0 HP.
  Qed.
  #[global] Instance as_Rep_fractional P :
    (∀ p, Fractional (λ q, P q p)) → Fractional (λ q, as_Rep (P q)).
  Proof.
    intros HP q1 q2. constructor=>p. by rewrite monPred_at_sep /= HP.
  Qed.
  #[global] Instance as_Rep_as_fractional P q :
    (∀ p, AsFractional (P q p) (λ q, P q p) q) →
    AsFractional (as_Rep (P q)) (λ q, as_Rep (P q)) q.
  Proof. constructor. done. apply _. Qed.

  #[global] Instance as_Rep_cfractional {P : cQp.t -> ptr -> mpred} :
    CFractional1 P ->
    CFractional (fun q => as_Rep (P q)).
  Proof. intros HP q1 q2. constructor =>p. by rewrite monPred_at_sep /= HP. Qed.
  #[global] Instance as_Rep_as_cfractional (P : cQp.t -> ptr -> mpred) q :
    AsCFractional1 P ->
    AsCFractional (as_Rep (P q)) (λ q, as_Rep (P q)) q.
  Proof. solve_as_cfrac. Qed.

  #[global] Instance as_Rep_laterable (R : ptr -> mpred) :
    (∀ p, Laterable (R p)) -> Laterable (as_Rep R).
  Proof.
    rewrite/Laterable=>HR. constructor=>p/=.
    iIntros "R". iDestruct (HR with "R") as (R') "[R #close]".
    rewrite monPred_at_exist. iExists (pureR R').
    rewrite monPred_at_sep monPred_at_later/=. iFrame "R".
    rewrite monPred_at_intuitionistically monPred_at_wand.
    iIntros "!>" (p' ->%ptr_rel_elim).
    by rewrite monPred_at_later monPred_at_except_0/=.
  Qed.

  Lemma as_Rep_embed P : as_Rep (λ _, P) -|- embed P.
  Proof. constructor=>p /=. by rewrite monPred_at_embed. Qed.

  Lemma as_Rep_emp : as_Rep (λ p, emp) -|- emp.
  Proof. constructor => p. by rewrite monPred_at_emp. Qed.
  Lemma as_Rep_sep P Q : as_Rep (λ p, P p ** Q p) -|- as_Rep P ** as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_sep. Qed.

  (* NOTE this is not exposed as a hint *)
  Lemma as_Rep_observe P Q (o : forall p, Observe (P p) (Q p)) : Observe (as_Rep P) (as_Rep Q).
  Proof. apply: monPred_observe=>p. Qed.
  Lemma as_Rep_observe_2 P Q R (o : forall p, Observe2 (P p) (Q p) (R p)) :
    Observe2 (as_Rep P) (as_Rep Q) (as_Rep R).
  Proof. apply: monPred_observe_2=>p. Qed.

  #[global] Instance as_Rep_only_provable_observe Q (P : ptr → mpred) :
    (∀ p, Observe [| Q |] (P p)) → Observe [| Q |] (as_Rep P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_only_provable.
  Qed.
  #[global] Instance as_Rep_only_provable_observe_2 Q (P1 P2 : ptr → mpred) :
    (∀ p, Observe2 [| Q |] (P1 p) (P2 p)) →
    Observe2 [| Q |] (as_Rep P1) (as_Rep P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma as_Rep_obs f P :
    (∀ p, f p |-- f p ** [| P |]) →
    as_Rep f |-- as_Rep f ** [| P |].
  Proof.
    intros. apply observe_elim, as_Rep_only_provable_observe =>p. exact: observe_intro.
  Qed.

  Lemma as_Rep_and P Q : as_Rep (λ p, P p //\\ Q p) -|- as_Rep P //\\ as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_and. Qed.

  Lemma as_Rep_or P Q : as_Rep (λ p, P p \\// Q p) -|- as_Rep P \\// as_Rep Q.
  Proof. constructor=>p. by rewrite monPred_at_or. Qed.

  Lemma as_Rep_wand P Q : as_Rep (λ p, P p -* Q p) -|- as_Rep P -* as_Rep Q.
  Proof.
    constructor=>p /=. split'.
    - rewrite monPred_at_wand. iIntros "H" (p' ->%ptr_rel_elim) "/= P".
      iApply ("H" with "P").
    - apply monPred_wand_force.
  Qed.

  Lemma as_Rep_pure (P : Prop) : as_Rep (fun _ => bi_pure P) -|- bi_pure P.
  Proof.
    rewrite /as_Rep.
    split; intro; rewrite /=. by rewrite monPred_at_pure /=.
  Qed.

  Lemma as_Rep_exist {T} (P : T -> ptr -> mpred) :
    as_Rep (λ p, Exists x, P x p) -|- Exists x, as_Rep (P x).
  Proof. constructor=>p /=. by rewrite monPred_at_exist. Qed.

  Lemma as_Rep_forall {T} (P : T -> ptr -> mpred) :
    as_Rep (λ p, Forall x, P x p) -|- Forall x, as_Rep (P x).
  Proof. constructor=>p /=. by rewrite monPred_at_forall. Qed.

  Lemma as_Rep_pers P : as_Rep (λ p, <pers> P p) -|- <pers> (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_persistently. Qed.

  Lemma as_Rep_bupd P : as_Rep (λ p, |==> P p) -|- |==> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_bupd. Qed.

  Lemma as_Rep_fupd P E1 E2 : as_Rep (λ p, |={E1,E2}=> P p) -|- |={E1,E2}=> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_fupd. Qed.

  Lemma as_Rep_intuitionistically P : as_Rep (λ p, □ P p) -|- □ as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_intuitionistically. Qed.

  Lemma as_Rep_intuitionistically_if b P : as_Rep (λ p, □?b P p) -|- □?b as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_intuitionistically_if. Qed.

  Lemma as_Rep_except_0 P : as_Rep (λ p, bi_except_0 (P p)) -|- bi_except_0 (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_except_0. Qed.

  Lemma as_Rep_affinely P : as_Rep (λ p, <affine> P p) -|- <affine> (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_affinely. Qed.

  Lemma as_Rep_affinely_if b P : as_Rep (λ p, <affine>?b P p) -|- <affine>?b (as_Rep P).
  Proof. constructor=>p /=. by rewrite monPred_at_affinely_if. Qed.

  Lemma as_Rep_big_sepL {T} (l : list T) (F : nat -> T -> ptr -> mpred) :
    as_Rep (λ p, [∗list] i ↦ x ∈ l, F i x p) -|- [∗list] i ↦ x ∈ l, as_Rep (F i x).
  Proof. constructor=>p /=. by rewrite monPred_at_big_sepL. Qed.

  Lemma as_Rep_later P : as_Rep (λ p, |> P p) -|- |> as_Rep P.
  Proof. constructor=>p /=. by rewrite monPred_at_later. Qed.

  Lemma as_Rep_internal_eq (P Q : mpred) : as_Rep (λ _, P ≡ Q) -|- P ≡ Q.
  Proof. constructor=>p /=. by rewrite monPred_at_internal_eq. Qed.

  Lemma Rep_wand_force (R1 R2 : Rep) p : (R1 -* R2) p -|- R1 p -* R2 p.
  Proof. split'. apply monPred_wand_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_impl_force (R1 R2 : Rep) p : (R1 -->> R2) p -|- R1 p -->> R2 p.
  Proof. split'. apply monPred_impl_force. by iIntros "a" (? <-%ptr_rel_elim). Qed.
  Lemma Rep_at_wand_iff (P Q : Rep) p :
    (P ∗-∗ Q) p ⊣⊢ (P p ∗-∗ Q p).
  Proof. by rewrite /bi_wand_iff monPred_at_and !Rep_wand_force. Qed.

  Lemma as_Rep_only_provable (P : Prop) : as_Rep (fun _ => [| P |]) -|- [| P |].
  Proof.
    rewrite only_provable.unlock as_Rep_affinely /as_Rep.
    split; intro; rewrite /=. by rewrite !monPred_at_affinely monPred_at_pure /=.
  Qed.

  Import rep_defs.INTERNAL.

  #[global] Instance _offsetR_ne o n : Proper (dist n ==> dist n) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _offsetR_proper o : Proper ((≡) ==> (≡)) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _offsetR_mono o : Proper ((⊢) ==> (⊢)) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _offsetR_flip_mono o : Proper (flip (⊢) ==> flip (⊢)) (_offsetR o).
  Proof. unfold_at. solve_proper. Qed.

  #[global] Instance _offsetR_persistent o (r : Rep) : Persistent r -> Persistent (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_affine o (r : Rep) : Affine r -> Affine (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_timeless o (r : Rep) : Timeless r → Timeless (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.
  #[global] Instance _offsetR_laterable o (r : Rep) : Laterable r → Laterable (o |-> r).
  Proof. rewrite _offsetR_eq. apply _. Qed.

  Lemma _offsetR_offsetR (o1 o2 : offset) R : o1 |-> (o2 |-> R) -|- o1 ,, o2 |-> R.
  Proof.
    rewrite !_offsetR_eq/=.
    f_equiv. by intro; rewrite offset_ptr_dot.
  Qed.

  Lemma _offsetR_emp o : o |-> emp ⊣⊢ emp.
  Proof.
    rewrite _offsetR_eq.
    constructor=> p /=. by rewrite !monPred_at_emp.
  Qed.
  Lemma _offsetR_sep o r1 r2 :
    o |-> (r1 ** r2) -|- o |-> r1 ** o |-> r2.
  Proof.
    rewrite !_offsetR_eq -as_Rep_sep.
    constructor=> p /=. by rewrite monPred_at_sep.
  Qed.
  Lemma _offsetR_pure (o : offset) (P : Prop) :
    o |-> (bi_pure P) -|- bi_pure P.
  Proof.
    rewrite _offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_pure.
  Qed.

  Lemma _offsetR_only_provable (o : offset) (P : Prop) :
    o |-> [| P |] -|- [| P |].
  Proof.
    rewrite _offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_only_provable.
  Qed.

  Lemma _offsetR_and (o : offset) P Q :
    o |-> (P //\\ Q) -|- o |-> P //\\ o |-> Q.
  Proof.
    rewrite !_offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_and.
  Qed.

  Lemma _offsetR_or (o : offset) P Q :
    o |-> (P \\// Q) -|- o |-> P \\// o |-> Q.
  Proof.
    rewrite !_offsetR_eq/=.
    by constructor=> p/=; rewrite !monPred_at_or.
  Qed.

  Lemma _offsetR_wand o (P Q : Rep) :
      o |-> (P -* Q) -|- o |-> P -* o |-> Q.
  Proof.
    rewrite /= !_offsetR_eq /=.
    constructor=> p/=. by rewrite !Rep_wand_force.
  Qed.

  Lemma _offsetR_exists o {T} (P : T -> Rep) :
      o |-> (Exists v : T, P v) -|- Exists v, o |-> (P v).
  Proof.
    rewrite _offsetR_eq /as_Rep/=.
    constructor =>p; rewrite /= !monPred_at_exist.
    f_equiv=>x. by rewrite _offsetR_eq.
  Qed.

  Lemma _offsetR_forall o T (P : T -> Rep) :
    o |-> (Forall x, P x) -|- Forall x, o |-> (P x).
  Proof.
    rewrite _offsetR_eq /as_Rep/=.
    constructor =>p; rewrite /= !monPred_at_forall.
    f_equiv=>x. by rewrite _offsetR_eq.
  Qed.

  Lemma _offsetR_pers o R : o |-> (<pers> R) -|- <pers> o |-> R.
  Proof. rewrite !_offsetR_eq. by constructor=> p/=; rewrite !monPred_at_persistently. Qed.

  Lemma _offsetR_bupd o R : o |-> (|==> R) -|- |==> o |-> R.
  Proof. by rewrite !_offsetR_eq /as_Rep; constructor => p /=; rewrite !monPred_at_bupd. Qed.

  Lemma _offsetR_fupd o R E1 E2 : o |-> (|={E1,E2}=> R) -|- |={E1,E2}=> o |-> R.
  Proof. by rewrite !_offsetR_eq /as_Rep; constructor => p /=; rewrite !monPred_at_fupd. Qed.

  Lemma _offsetR_intuitionistically o (R : Rep) : o |-> (□ R) ⊣⊢ □ (o |-> R).
  Proof. by rewrite !_offsetR_eq; constructor => p /=; rewrite !monPred_at_intuitionistically. Qed.

  Lemma _offsetR_intuitionistically_if o b R : o |-> (□?b R) -|- □?b (o |-> R).
  Proof. by destruct b => //=; rewrite /= _offsetR_intuitionistically. Qed.

  Lemma _offsetR_except_0 o R : o |-> (bi_except_0 R) -|- bi_except_0 (o |-> R).
  Proof. by rewrite !_offsetR_eq; constructor => p /=; rewrite !monPred_at_except_0. Qed.

  Lemma _offsetR_affinely (o : offset) R : o |-> (<affine> R) -|- <affine> o |-> R.
  Proof. by rewrite !_offsetR_eq /as_Rep; constructor => p/=; rewrite !monPred_at_affinely. Qed.

  Lemma _offsetR_affinely_if b (o : offset) R : o |-> (<affine>?b R) -|- <affine>?b o |-> R.
  Proof. by destruct b => //; rewrite _offsetR_affinely. Qed.

  Lemma _offsetR_big_sepL (o : offset) {T} (Rs : list T) : forall F,
    o |-> ([∗list] i ↦ x ∈ Rs , F i x) -|- [∗list] i ↦ x ∈ Rs , o |-> (F i x).
  Proof.
    induction Rs; simpl; intros.
    - by rewrite _offsetR_emp.
    - by rewrite _offsetR_sep IHRs.
  Qed.

  Lemma _offsetR_later o R : o |-> (|> R) -|- |> o |-> R.
  Proof.
    rewrite !_offsetR_eq. constructor=>p/=. by rewrite !monPred_at_later.
  Qed.

  #[global] Instance _offsetR_fractional o (r : Qp → Rep) :
    Fractional r → Fractional (λ q, o |-> r q).
  Proof. by move => H q1 q2; rewrite fractional _offsetR_sep. Qed.
  #[global] Instance _offsetR_as_fractional o (R : Rep) (r : Qp → Rep) q
      `{!AsFractional R r q} :
    AsFractional (o |-> R) (λ q, o |-> r q) q.
  Proof. constructor; [by erewrite as_fractional | apply _]. Qed.

  #[global] Instance _offsetR_cfractional {R : cQp.t -> Rep} o :
    CFractional R ->
    CFractional (fun q => _offsetR o (R q)).
  Proof. intros HR q1 q2. constructor =>p. by rewrite cfractional _offsetR_sep. Qed.
  #[global] Instance _offsetR_as_cfractional o (P : Rep) (R : cQp.t -> Rep) q :
    AsCFractional P R q ->
    AsCFractional (_offsetR o P) (λ q, _offsetR o (R q)) q.
  Proof. constructor. by rewrite -as_cfractional. apply _. Qed.

  #[global] Instance _offsetR_observe {o} {Q R : Rep} :
    Observe Q R ->
    Observe (o |-> Q) (o |-> R).
  Proof. move->. by rewrite /Observe -_offsetR_pers. Qed.

  #[global] Instance _offsetR_observe_2 {o} {Q R1 R2 : Rep} :
    Observe2 Q R1 R2 ->
    Observe2 (o |-> Q) (o |-> R1) (o |-> R2).
  Proof.
    rewrite /Observe2.
    move->. by rewrite /Observe2 _offsetR_wand _offsetR_pers. Qed.

  #[global] Instance _offsetR_observe_only_provable Q o (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (o |-> R).
  Proof. rewrite -{2}_offsetR_only_provable. apply _. Qed.
  #[global] Instance _offsetR_observe_2_only_provable Q o (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (o |-> R1) (o |-> R2).
  Proof. rewrite -{2}_offsetR_only_provable. apply _. Qed.

  #[global] Instance _offsetR_observe_pure Q o (R : Rep) :
    Observe [! Q !] R → Observe [! Q !] (o |-> R).
  Proof. rewrite -{2}_offsetR_pure. apply _. Qed.
  #[global] Instance _offsetR_observe_2_pure Q o (R1 R2 : Rep) :
    Observe2 [! Q !] R1 R2 → Observe2 [! Q !] (o |-> R1) (o |-> R2).
  Proof. rewrite -{2}_offsetR_pure. apply _. Qed.

  Lemma _offsetR_obs o r P :
    r |-- r ** [| P |] →
    o |-> r |-- o |-> r ** [| P |].
  Proof.
    intros. apply observe_elim, _offsetR_observe_only_provable. exact: observe_intro.
  Qed.
  (* Pulled in from plogic. *)
  Lemma _offsetR_id (R : Rep) :
    _offsetR o_id R -|- R.
  Proof.
    rewrite _offsetR_eq.
    constructor=>/= p.
    by rewrite offset_ptr_id.
  Qed.

  Lemma _offsetR_dot (o1 o2 : offset) (R : Rep) :
    _offsetR o1 (_offsetR o2 R) -|- _offsetR (o1 ,, o2) R.
  Proof.
    constructor =>p/=.
    by rewrite !_offsetR_eq/= offset_ptr_dot.
  Qed.

  #[global] Instance _at_ne p {n} : Proper (dist n ==> dist n) (_at p).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _at_proper {p} : Proper ((≡) ==> (≡)) (_at p).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _at_mono {p} : Proper ((⊢) ==> (⊢)) (_at p).
  Proof. unfold_at. solve_proper. Qed.
  #[global] Instance _at_flip_mono {p} : Proper (flip (⊢) ==> flip (⊢)) (_at p).
  Proof. unfold_at; move => r1 r2 HR/=. solve_proper. Qed.

  #[global] Instance _at_persistent {P base} : Persistent P -> Persistent (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_affine {P base} : Affine P -> Affine (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_timeless {P base} : Timeless P -> Timeless (_at base P).
  Proof. rewrite _at_eq. apply _. Qed.
  #[global] Instance _at_laterable p (P : Rep) : Laterable P → Laterable (p |-> P).
  Proof. rewrite _at_eq. apply _. Qed.

  Lemma _at_as_Rep p (Q : ptr → mpred) : p |-> (as_Rep Q) ⊣⊢ Q p.
  Proof. by rewrite _at_eq. Qed.

  (* Prefer [_at_as_Rep] *)
  Lemma _at_loc p (R : Rep) : p |-> R -|- R p.
  Proof. by rewrite _at_eq. Qed.

  Lemma _at_emp p : p |-> emp -|- emp.
  Proof. by rewrite _at_loc monPred_at_emp. Qed.

  Lemma _at_exists p {T} (P : T -> Rep) :
      p |-> (Exists v : T, P v) -|- Exists v, p |-> (P v).
  Proof. by rewrite _at_loc monPred_at_exist; setoid_rewrite _at_loc. Qed.

  Lemma _at_forall p T (P : T -> Rep) :
    p |-> (Forall x, P x) -|- Forall x, p |-> (P x).
  Proof. by rewrite _at_loc monPred_at_forall; setoid_rewrite _at_loc. Qed.

  Lemma _at_only_provable p P :
      p |-> [| P |] -|- [| P |].
  Proof. by rewrite _at_loc monPred_at_only_provable. Qed.

  Lemma _at_pure p (P : Prop) :
      p |-> [! P !] -|- [! P !].
  Proof. by rewrite _at_loc monPred_at_pure. Qed.

  Lemma _at_sep p (P Q : Rep) :
      p |-> (P ** Q) -|- p |-> P ** p |-> Q.
  Proof. by rewrite !_at_loc monPred_at_sep. Qed.

  Lemma _at_and p (P Q : Rep) :
      p |-> (P //\\ Q) -|- p |-> P //\\ p |-> Q.
  Proof. by rewrite !_at_loc monPred_at_and. Qed.

  Lemma _at_or p (P Q : Rep) :
      p |-> (P \\// Q) -|- p |-> P \\// p |-> Q.
  Proof. by rewrite !_at_loc monPred_at_or. Qed.

  Lemma _at_wand p (P Q : Rep) :
      p |-> (P -* Q) -|- p |-> P -* p |-> Q.
  Proof. by rewrite !_at_loc Rep_wand_force. Qed.

  Lemma _at_impl p R1 R2 : p |-> (R1 -->> R2) -|- p |-> R1 -->> p |-> R2.
  Proof. by rewrite !_at_loc Rep_impl_force. Qed.

  Lemma _at_pers p R : p |-> (<pers> R) -|- <pers> p |-> R.
  Proof. by rewrite !_at_loc monPred_at_persistently. Qed.

  Lemma _at_bupd p R : p |-> (|==> R) -|- |==> p |-> R.
  Proof. by rewrite !_at_loc monPred_at_bupd. Qed.

  Lemma _at_fupd p R E1 E2 : p |-> (|={E1,E2}=> R) -|- |={E1,E2}=> p |-> R.
  Proof. by rewrite !_at_loc monPred_at_fupd. Qed.

  Lemma _at_intuitionistically p (R : Rep) : p |-> □ R ⊣⊢ □ (p |-> R).
  Proof. by rewrite !_at_eq; rewrite monPred_at_intuitionistically. Qed.
  Lemma _at_intuitionistically_if (p : ptr) b R : p |-> (□?b R) -|- □?b (p |-> R).
  Proof. destruct b => //=. by rewrite _at_intuitionistically. Qed.

  Lemma _at_except_0 (p : ptr) R : p |-> bi_except_0 R -|- bi_except_0 (p |-> R).
  Proof. by rewrite !_at_eq monPred_at_except_0. Qed.

  Lemma _at_affinely (p : ptr) R : p |-> <affine> R -|- <affine> p |-> R.
  Proof. by rewrite !_at_eq monPred_at_affinely. Qed.

  Lemma _at_affinely_if b (p : ptr) R : p |-> <affine>?b R -|- <affine>?b p |-> R.
  Proof. by destruct b => //; rewrite !_at_eq monPred_at_affinely. Qed.

  Lemma _at_later p R : p |-> |> R -|- |> p |-> R.
  Proof. by rewrite !_at_eq; rewrite monPred_at_later. Qed.

  Lemma _at_internal_eq p {A : ofe} x y : p |-> (x ≡@{A} y) -|- x ≡ y.
  Proof. by rewrite _at_loc monPred_at_internal_eq. Qed.

  Lemma _at_offsetR p (o : offset) (r : Rep) :
      _at p (_offsetR o r) -|- _at (p ,, o) r.
  Proof. rewrite !_at_loc /flip. by unfold_at. Qed.

  (** Big ops *)
  Lemma _at_big_sepL A p : forall (xs : list A) (Φ : nat -> A -> Rep),
      p |-> ([∗ list] i↦x∈xs, Φ i x) -|- ([∗ list] i↦x∈xs, p |-> (Φ i x)).
  Proof.
    elim => /=.
    - move => ?; by rewrite _at_emp.
    - move => x xs IH ?. by rewrite _at_sep IH.
  Qed.

  Lemma _at_sepSPs p (xs : list Rep) : p |-> ([∗] xs) -|- [∗] map (_at p) xs.
  Proof. by rewrite _at_big_sepL big_sepL_fmap. Qed.

  Lemma _at_big_sepS `{Countable A} p (X : gset A) (Φ : A -> Rep) :
    p |-> ([∗ set] x ∈ X, Φ x) -|- [∗ set] x ∈ X, p |-> Φ x.
  Proof.
    rewrite _at_eq monPred_at_big_sepS.
    by apply big_opS_proper => x _; rewrite _at_eq. (*TODO: AUTO(gs) missing proper instance*)
  Qed.

  Lemma _at_big_sepM `{Countable K} {A} p (m : gmap K A) (Φ : K → A → Rep) :
    p |-> ([∗ map] k↦x ∈ m, Φ k x) -|- [∗ map] k↦x ∈ m, p |-> Φ k x.
  Proof.
    rewrite _at_eq monPred_at_big_sepM.
    by apply big_opM_proper => k x _; rewrite _at_eq.
  Qed.

  Lemma _at_big_sepMS `{Countable A} p (X : gmultiset A) (Φ : A → Rep) :
    p |-> ([∗ mset] x ∈ X, Φ x) -|- [∗ mset] x ∈ X, p |-> Φ x.
  Proof.
    rewrite _at_eq monPred_at_big_sepMS.
    by apply big_opMS_proper => x _; rewrite _at_eq.
  Qed.

  #[global] Instance _at_fractional (r : Qp → Rep) p `{!Fractional r} :
    Fractional (λ q, p |-> (r q)).
  Proof.
    intros q1 q2; by rewrite fractional _at_sep.
  Qed.
  #[global] Instance _at_as_fractional R (r : Qp → Rep) q p
      `{!AsFractional R r q} :
    AsFractional (p |-> R) (λ q, p |-> r q) q.
  Proof. constructor; [by erewrite as_fractional | apply _]. Qed.

  #[global] Instance _at_cfractional {R : cQp.t -> Rep} p :
    CFractional R ->
    CFractional (fun q => _at p (R q)).
  Proof. intros HR q1 q2. by rewrite cfractional _at_sep. Qed.
  #[global] Instance _at_as_cfractional p (P : Rep) (R : cQp.t -> Rep) q :
    AsCFractional P R q ->
    AsCFractional (_at p P) (λ q, _at p (R q)) q.
  Proof. constructor. by rewrite -as_cfractional. apply _. Qed.

  #[global] Instance _at_observe {p} {Q R : Rep} :
    Observe Q R ->
    Observe (p |-> Q) (p |-> R).
  Proof. move->. by rewrite /Observe _at_pers. Qed.

  #[global] Instance _at_observe_2 {p} {Q R1 R2 : Rep} :
    Observe2 Q R1 R2 ->
    Observe2 (p |-> Q) (p |-> R1) (p |-> R2).
  Proof. move->. by rewrite /Observe2 _at_wand _at_pers. Qed.

  #[global] Instance _at_observe_only_provable Q p (R : Rep) :
    Observe [| Q |] R → Observe [| Q |] (p |-> R).
  Proof. rewrite -_at_only_provable. apply _. Qed.
  #[global] Instance _at_observe_2_only_provable Q p (R1 R2 : Rep) :
    Observe2 [| Q |] R1 R2 → Observe2 [| Q |] (p |-> R1) (p |-> R2).
  Proof. rewrite -_at_only_provable. apply _. Qed.

  #[global] Instance _at_observe_pure Q p (R : Rep) :
    Observe [! Q !] R → Observe [! Q !] (p |-> R).
  Proof. rewrite -_at_pure. apply _. Qed.
  #[global] Instance _at_observe_2_pure Q p (R1 R2 : Rep) :
    Observe2 [! Q !] R1 R2 → Observe2 [! Q !] (p |-> R1) (p |-> R2).
  Proof. rewrite -_at_pure. apply _. Qed.

  #[global] Instance observe_2_internal_eq_at {A : ofe} x y R1 R2 p :
    Observe2 (x ≡@{A} y) R1 R2 -> Observe2 (x ≡ y) (p |-> R1) (p |-> R2).
  Proof. rewrite !_at_loc. apply _. Qed.
  #[global] Instance observe_2_later_internal_eq_at {A : ofe} x y R1 R2 p :
    Observe2 (|> (x ≡@{A} y)) R1 R2 ->
    Observe2 (|> (x ≡ y)) (p |-> R1) (p |-> R2).
  Proof. rewrite !_at_loc. apply _. Qed.

  Lemma Rep_equiv_at {P Q : Rep} :
    (forall p : ptr, p |-> P -|- p |-> Q) <->
    P -|- Q.
  Proof.
    setoid_rewrite _at_loc; split; first by constructor.
    by move => /[swap] ? <-.
  Qed.

  Lemma Rep_entails_at {P Q : Rep} :
    (forall p : ptr, p |-> P |-- p |-> Q) <->
    P |-- Q.
  Proof.
    setoid_rewrite _at_loc; split; first by constructor.
    by move => /[swap] ? <-.
  Qed.

  Lemma Rep_emp_valid {P : Rep} :
    (forall p : ptr, |-- p |-> P) <->
    |-- P.
  Proof.
    rewrite /bi_emp_valid -Rep_entails_at.
    by setoid_rewrite _at_emp.
  Qed.

  Lemma _at_obs p (r : Rep) P :
    r |-- r ** [| P |] →
    p |-> r |-- p |-> r ** [| P |].
  Proof. intros. apply observe_elim, _at_observe_only_provable. exact: observe_intro. Qed.

  #[global] Instance pureR_ne : NonExpansive pureR.
  Proof. solve_proper. Qed.
  #[global] Instance pureR_proper : Proper ((≡) ==> (≡)) pureR.
  Proof. solve_proper. Qed.
  #[global] Instance pureR_mono : Proper ((⊢) ==> (⊢)) pureR.
  Proof. by constructor. Qed.
  #[global] Instance pureR_flip_momo : Proper (flip (⊢) ==> flip (⊢)) pureR.
  Proof. by constructor. Qed.

  #[global] Instance pureR_persistent (P : mpred) :
    Persistent P -> Persistent (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_affine (P : mpred) :
    Affine P -> Affine (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_timeless (P : mpred) :
    Timeless P → Timeless (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_fractional (P : Qp → mpred) :
    Fractional P → Fractional (λ q, pureR (P q)).
  Proof. apply _. Qed.
  #[global] Instance pureR_as_fractional P Φ q :
    AsFractional P Φ q →
    AsFractional (pureR P) (λ q, pureR (Φ q)) q.
  Proof. intros [??]. constructor. done. apply _. Qed.
  #[global] Instance pureR_cfractional (P : cQp.t → mpred) :
    CFractional P -> CFractional (fun q => pureR (P q)).
  Proof. apply _. Qed.
  #[global] Instance pureR_as_cfractional (P : mpred) (F : cQp.t -> mpred) q :
    AsCFractional P F q →
    AsCFractional (pureR P) (fun q => pureR (F q)) q.
  Proof. intros [??]. constructor. done. apply _. Qed.

  #[global] Instance pureR_objective P : Objective (pureR P).
  Proof. done. Qed.

  #[global] Instance pureR_laterable P : Laterable P → Laterable (pureR P).
  Proof. intros. exact: as_Rep_laterable. Qed.

  Lemma pureR_persistently P : pureR (<pers> P) -|- <pers> pureR P.
  Proof. constructor=>p /=. by rewrite monPred_at_persistently. Qed.

  Lemma pureR_only_provable P : pureR [| P |] ⊣⊢ [| P |].
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_only_provable.
    - constructor=>p. by rewrite monPred_at_only_provable.
  Qed.

  Lemma pureR_embed P : pureR P -|- embed P.
  Proof. exact: as_Rep_embed. Qed.

  Lemma pureR_emp : pureR emp -|- emp.
  Proof. exact: as_Rep_emp. Qed.
  Lemma pureR_sep (P Q : mpred) : pureR (P ** Q) -|- pureR P ** pureR Q.
  Proof. exact: as_Rep_sep. Qed.

  Lemma pureR_and (P Q : mpred) : pureR (P //\\ Q) -|- pureR P //\\ pureR Q.
  Proof. exact: as_Rep_and. Qed.

  Lemma pureR_or (P Q : mpred) : pureR (P \\// Q) -|- pureR P \\// pureR Q.
  Proof. exact: as_Rep_or. Qed.

  Lemma pureR_wand (P Q : mpred) : pureR (P -* Q) -|- pureR P -* pureR Q.
  Proof. exact: as_Rep_wand. Qed.

  Lemma pureR_exist {T} (P : T -> mpred) :
    pureR (Exists x, P x) -|- Exists x, pureR (P x).
  Proof. exact: as_Rep_exist. Qed.

  Lemma pureR_forall {T} (P : T -> mpred) :
    pureR (Forall x, P x) -|- Forall x, pureR (P x).
  Proof. exact: as_Rep_forall. Qed.

  Lemma pureR_pers (P : mpred) : pureR (<pers> P) -|- <pers> pureR P.
  Proof. exact: as_Rep_pers. Qed.

  Lemma pureR_bupd (P : mpred) : pureR (|==> P) -|- |==> pureR P.
  Proof. exact: as_Rep_bupd. Qed.

  Lemma pureR_fupd (P : mpred) E1 E2 : pureR (|={E1,E2}=> P) -|- |={E1,E2}=> pureR P.
  Proof. exact: as_Rep_fupd. Qed.

  Lemma pureR_intuitionistically (P : mpred) : pureR (□ P) -|- □ pureR P.
  Proof. exact: as_Rep_intuitionistically. Qed.

  Lemma pureR_intuitionistically_if b (P : mpred) : pureR (□?b P) -|- □?b pureR P.
  Proof. exact: as_Rep_intuitionistically_if. Qed.

  Lemma pureR_except_0 (P : mpred) : pureR (bi_except_0 P) -|- bi_except_0 (pureR P).
  Proof. exact: as_Rep_except_0. Qed.

  Lemma pureR_affinely (P : mpred) : pureR (<affine> P) -|- <affine> pureR P.
  Proof. exact: as_Rep_affinely. Qed.

  Lemma pureR_affinely_if b (P : mpred) : pureR (<affine>?b P) -|- <affine>?b pureR P.
  Proof. exact: as_Rep_affinely_if. Qed.

  Lemma pureR_big_sepL {T} (l : list T) F :
    pureR ([∗list] i ↦ x ∈ l , F i x) -|- [∗list] i ↦ x ∈ l , pureR (F i x).
  Proof. exact: as_Rep_big_sepL. Qed.

  Lemma pureR_later (P : mpred) : pureR (|> P) -|- |> pureR P.
  Proof. exact: as_Rep_later. Qed.

  Lemma pureR_internal_eq (P1 P2 : mpred) : pureR (P1 ≡ P2) -|- P1 ≡ P2.
  Proof. exact: as_Rep_internal_eq. Qed.

  #[global] Instance pureR_observe Q (P : mpred) :
    Observe [| Q |] P → Observe [| Q |] (pureR P).
  Proof. apply _. Qed.
  #[global] Instance pureR_observe_2 Q (P1 P2 : mpred) :
    Observe2 [| Q |] P1 P2 → Observe2 [| Q |] (pureR P1) (pureR P2).
  Proof. apply _. Qed.
  #[global] Instance pureR_observe_pure Q (P : mpred) :
    Observe [! Q !] P → Observe [! Q !] (pureR P).
  Proof.
    intros. apply monPred_observe=>p. by rewrite monPred_at_pure.
  Qed.
  #[global] Instance pureR_observe_2_pure Q (P1 P2 : mpred) :
    Observe2 [! Q !] P1 P2 → Observe2 [! Q !] (pureR P1) (pureR P2).
  Proof.
    intros. apply monPred_observe_2=>p. by rewrite monPred_at_pure.
  Qed.

  Lemma pureR_obs P Q :
    P |-- P ** [| Q |] →
    pureR P |-- pureR P ** [| Q |].
  Proof. intros. apply observe_elim, pureR_observe. exact: observe_intro. Qed.

  Lemma pureR_pure P : pureR ⌜P⌝ ⊣⊢ ⌜P⌝.
  Proof.
    split'.
    - rewrite (objective_objectively (pureR _)).
      rewrite monPred_objectively_unfold embed_forall.
      by rewrite (bi.forall_elim inhabitant) embed_pure.
    - constructor=>p. by rewrite monPred_at_pure.
  Qed.
  Definition pureR_True : pureR True ⊣⊢ True := pureR_pure _.
  Definition pureR_False : pureR False ⊣⊢ False := pureR_pure _.

  Lemma _at_pureR x (P : mpred) : _at x (pureR P) -|- P.
  Proof. by rewrite !_at_loc /pureR. Qed.

  Lemma _offsetR_pureR o P : o |-> (pureR P) -|- pureR P.
  Proof. by apply Rep_equiv_at => p; rewrite _at_offsetR !_at_pureR. Qed.

  (** As this isn't syntax-directed, we conservatively avoid
      registering it as an instance (which could slow down
      observations). It's handy under [#[local] Existing Instance
      _at_observe_pureR] to project a [pureR Q] conjunct out of
      representation predicates. *)
  Lemma _at_observe_pureR Q p (R : Rep) :
    Observe (pureR Q) R → Observe Q (p |-> R).
  Proof.
    rewrite /Observe=>->. rewrite -pureR_persistently _at_pureR. done.
  Qed.

  (** Introduce Observations at [Rep] by proving them more easily at [mpred] *)
  Lemma observe_at (Q P : Rep) :
    (∀ p : ptr, Observe (p |-> Q) (p |-> P)) ↔
    Observe Q P.
  Proof.
    split; intros; last exact: _at_observe.
    apply monPred_observe=> p. by rewrite -!_at_loc.
  Qed.

  Lemma observe_only_provable_at Q (P : Rep) :
    (∀ p : ptr, Observe [| Q |] (p |-> P)) ↔
    Observe [| Q |] P.
  Proof.
    rewrite -observe_at.
    apply iff_forall => p. by rewrite _at_only_provable.
  Qed.

  Lemma observe_2_at (Q P1 P2 : Rep) :
    (∀ p : ptr, Observe2 (p |-> Q) (p |-> P1) (p |-> P2)) ↔
    Observe2 Q P1 P2.
  Proof.
    split; intros; last exact: _at_observe_2.
    apply monPred_observe_2=> p. by rewrite -!_at_loc.
  Qed.

  Lemma observe_2_only_provable_at Q (P1 P2 : Rep) :
    (∀ p : ptr, Observe2 [| Q |] (p |-> P1) (p |-> P2)) ↔
    Observe2 [| Q |] P1 P2.
  Proof.
    rewrite -observe_2_at.
    apply iff_forall => p. by rewrite _at_only_provable.
  Qed.

End with_cpp.

#[global] Typeclasses Opaque pureR as_Rep.

(** * Proof mode instances *)

(** We provide [_at], [_offsetR], and [pureR] instances for several
proof mode classes. Here's a subset, displayed here for [_at]:

- [IntoSep], [FromSep] for [loc |-> R1 ** R2]

- [IntoOr], [FromOr] for [loc |-> R1 \\// R2]

- [IntoAnd], [FromAnd] for [loc |-> R1 //\\ R2]

- [Frame] framing around [loc |-> R] if you can frame around [R]

Additional instances are available in

- [bedrock.proofmode.cpp._at_as_Rep]

- [bedrock.proofmode.cpp._at_pureR]

The instances in [bedrock.proofmode.cpp._at_eq_cinv] are, like the
ones here, enabled by requiring [bedrock.auto.cpp]. *)

(** * Instances for [_at] *)
Section _at_instances.
  Context `{Σ : cpp_logic}.
  Implicit Types l : ptr.
  Implicit Types R : Rep.

  (** Framing between [P] and [_at p (pureR P)]. *)
  Lemma test_before l P : l |-> pureR P |-- P.
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_at_pureR b l P :
    Frame b (l |-> pureR P) P emp | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite /Frame _at_pureR. by rewrite bi.intuitionistically_if_elim right_id.
  Qed.
  Lemma test_after l P : l |-> pureR P |-- P.
  Proof. by iIntros "$". Abort.

  Lemma test_before l (P : mpred) : P |-- l |-> pureR P.
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_pureR_at b l (P : mpred) :
    Frame b P (l |-> pureR P) emp | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite /Frame _at_pureR. by rewrite bi.intuitionistically_if_elim right_id.
  Qed.
  Lemma test_after l (P : mpred) : P |-- l |-> pureR P.
  Proof. by iIntros "$". Abort.

  (** TODO (PDS): The following two instances suggest we should
      refactor and, perhaps, reproduce some of the monpred proofmode
      machinery for [_at]. We're repeating things that the proofmode
      already knows how to do. *)
  Lemma test_before l (P : mpred) R : P |-- l |-> (pureR P ** R).
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_at_pureR_l l b (P1 P2 Q : mpred) R :
    Frame b P1 (P2 ** l |-> R) Q ->
    Frame b P1 (l |-> (pureR P2 ** R)) Q | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof. rewrite/Frame. by rewrite _at_sep _at_pureR. Qed.
  Lemma test_after l (P : mpred) R : P |-- l |-> (pureR P ** R).
  Proof. iIntros "$". Abort.

  Lemma test_before l (P : mpred) R : P |-- l |-> (R ** pureR P).
  Proof. Fail iIntros "$". Abort.
  #[global] Instance frame_at_pureR_r l b (P1 P2 Q : mpred) R :
    Frame b P1 (l |-> R ** P2) Q ->
    Frame b P1 (l |-> (R ** pureR P2)) Q | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof. rewrite/Frame. by rewrite _at_sep _at_pureR. Qed.
  Lemma test_after l (P : mpred) R : P |-- l |-> (R ** pureR P).
  Proof. iIntros "$". Abort.

  (** [IntoExist], [FromExist] *)
  Lemma test_before {A} l (Φ : A → Rep) :
    l |-> (Exists x, Φ x) |-- Exists x, l |-> Φ x.
  Proof. Fail iDestruct 1 as (x) "HΦ". Abort.
  Lemma test_before {A} l (Φ : A → Rep) :
    Exists x, l |-> Φ x |-- l |-> (Exists x, Φ x).
  Proof. iDestruct 1 as (x) "HΦ". Fail iExists x. Abort.

  #[global] Instance into_exist_at {A} {f} l R (Φ : A → Rep) :
    IntoExist R Φ f → IntoExist (l |-> R) (λ x, l |-> Φ x) f.
  Proof. intros H. by rewrite /IntoExist H _at_exists. Qed.
  #[global] Instance from_exist_at {A} l R (Φ : A → Rep) :
    FromExist R Φ → FromExist (l |-> R) (λ x, l |-> Φ x).
  Proof. intros H. by rewrite/FromExist -H _at_exists. Qed.

  Lemma test_after {A} l (Φ : A → Rep) :
    l |-> (Exists x, Φ x) |-- Exists x, l |-> Φ x.
  Proof. iDestruct 1 as (x) "HΦ". Abort.
  Lemma test_after {A} l (Φ : A → Rep) :
    Exists x, l |-> Φ x |-- l |-> (Exists x, Φ x).
  Proof. iDestruct 1 as (x) "HΦ". iExists x. Abort.

  (** [IntoForall], [FromForall] *)
  Lemma test_before {A} l (Φ : A → Rep) :
    l |-> (Forall x, Φ x) |-- Forall x, l |-> Φ x.
  Proof. iIntros "HΦ" (x). Fail iSpecialize ("HΦ" $! x). Abort.
  Lemma test_before {A} l (Φ : A → Rep) :
    Forall x, l |-> Φ x |-- l |-> Forall x, Φ x.
  Proof. Fail iIntros "HΦ" (x). Abort.

  #[global] Instance into_forall_at {A} l R (Φ : A → Rep) :
    IntoForall R Φ → IntoForall (l |-> R) (λ x, l |-> Φ x).
  Proof. intros H. by rewrite /IntoForall H _at_forall. Qed.
  #[global] Instance from_forall_at {A} l R (Φ : A → Rep) name :
    FromForall R Φ name → FromForall (l |-> R) (λ x, l |-> Φ x) name.
  Proof. intros H. by rewrite /FromForall -_at_forall H. Qed.

  Lemma test_after {A} l (Φ : A → Rep) :
    l |-> (Forall x, Φ x) |-- Forall x, l |-> Φ x.
  Proof. iIntros "HΦ" (x). iSpecialize ("HΦ" $! x). Abort.
  Lemma test_after {A} l (Φ : A → Rep) :
    Forall x, l |-> Φ x |-- l |-> Forall x, Φ x.
  Proof. iIntros "H" (x). iApply "H". Abort.

  (* [ElimModal] instance.
     NOTE Instances like this one that generate sub-derivations using [pureR] require
     corresponding instances for [pureR] (see below).
   *)
  #[global] Instance _at_elim_modal (pt : ptr) ϕ p p' P P' Q Q' :
    ElimModal ϕ p p' P P' (pureR Q) (pureR Q') ->
    ElimModal ϕ p p' (_at pt P) (_at pt P') Q Q'.
  Proof.
    intros H HPQ. apply H, bi.wand_intro_r in HPQ.
    rewrite -!_at_intuitionistically_if HPQ !_at_wand !_at_pureR.
    iIntros "[A B]". by iApply "A".
  Qed.

  (* [IntoPure] instance. *)
  Lemma test_before {P : Prop} (p : ptr) : _at p (bi_pure P) |-- True.
  Proof. Fail iIntros "%". Abort.

  #[global] Instance _at_into_pure {p P T} : IntoPure P T -> IntoPure (_at p P) T.
  Proof. by red; intros ->; rewrite _at_pure. Qed.

  Lemma test_after {P : Prop} (p : ptr) : _at p (bi_pure P) |-- True.
  Proof. iIntros "%". Abort.

  Lemma test_before {P : Prop} (p : ptr) : ⊢@{mpredI} _at p (bi_pure P).
  Proof. iIntros. Fail iPureIntro. Abort.

  #[global] Instance _at_from_pure {a p R T} (H : FromPure a R T) : FromPure a (_at p R) T.
  Proof. by red; red in H; rewrite -H _at_affinely_if _at_pure. Qed.

  Lemma test_after {P : Prop} (p : ptr) : ⊢@{mpredI} _at p (bi_pure P).
  Proof. iIntros. iPureIntro. Abort.

  (* [IsExcept0] *)
  #[global] Instance is_except0_at {R p} (H : IsExcept0 R) : IsExcept0 (_at p R).
  Proof. red. by rewrite -_at_except_0 H. Qed.

End _at_instances.

(** * Instances for [_offsetR] *)
Section _offsetR_instances.
  Context `{Σ : cpp_logic}.
  Implicit Types o : offset.
  Implicit Types R : Rep.
  Implicit Types P : mpred.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before o R1 R2 : o |-> (R1 ** R2) |-- o |-> R1 ** o |-> R2.
  Proof. Fail by iIntros "[$$]". Abort.

  #[global] Instance into_sep_offsetR o R R1 R2 :
    IntoSep R R1 R2 → IntoSep (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /IntoSep. by rewrite (into_sep R) _offsetR_sep.
  Qed.

  Lemma test_after o R1 R2 : o |-> (R1 ** R2) |-- o |-> R1 ** o |-> R2.
  Proof. by iIntros "[$$]". Abort.

  (** Feed the introduction pattern ["[H1|H2]"]. *)

  Lemma test_before o R1 R2 : o |-> (R1 \\// R2) |-- (o |-> R1 \\// o |-> R2).
  Proof. Fail by iIntros "[$|$]". Abort.

  #[global] Instance into_or_offsetR o R R1 R2 :
    IntoOr R R1 R2 -> IntoOr (o |-> R) (o |-> R1) (o |-> R2).
  Proof. intros. rewrite /IntoOr. by rewrite (into_or R) _offsetR_or. Qed.

  Lemma test_after o R1 R2 : o |-> (R1 \\// R2) |-- (o |-> R1 \\// o |-> R2).
  Proof. by iIntros "[$|$]". Abort.

  (** Feed the [iSplitL], [iSplitR], [iCombine] tactics. *)
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iSplitL "H1". Abort.
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iSplitR "H2". Abort.
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail by iCombine "H1 H2" as "H". Abort.

  #[global] Instance from_sep_offsetR o R R1 R2 :
    FromSep R R1 R2 → FromSep (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /FromSep. by rewrite -_offsetR_sep (from_sep R).
  Qed.

  #[global] Instance combine_sep_as_offsetR o R R1 R2 :
    CombineSepAs R1 R2 R → CombineSepAs (o |-> R1) (o |-> R2) (o |-> R) | 10.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -_offsetR_sep H.
  Qed.

  (* [CombineSepAs] does not have a base instance for [bi_sep] (unlike [FromSep]. *)
  #[global] Instance combine_sep_as_at_offsetR o R1 R2 :
    CombineSepAs (o |-> R1) (o |-> R2) (o |-> (R1 ** R2)) | 100.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -_offsetR_sep.
  Qed.

  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iSplitL "H1". Abort.
  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iSplitR "H2". Abort.
  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". by iCombine "H1 H2" as "H". Abort.

  (** Feed the [iLeft] and [iRight] tactics. *)
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". Fail by iLeft. Abort.

  Lemma test_before o R1 R2 : o |-> R2 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". Fail by iRight. Abort.

  #[global] Instance from_or_offsetR o R R1 R2 :
    FromOr R R1 R2 -> FromOr (o |-> R) (o |-> R1) (o |-> R2).
  Proof. intros. rewrite /FromOr. by rewrite -_offsetR_or (from_or R). Qed.

  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". by iLeft. Abort.

  Lemma test_after o R1 R2 : o |-> R2 |-- o |-> (R1 \\// R2).
  Proof. iIntros "H". by iRight. Abort.

  (** [IntoWand], [FromWand] *)
  Lemma test_before o R1 R2 : o |-> (R1 -* R2) |-- o |-> R1 -* o |-> R2.
  Proof. iIntros "H R1". Fail iApply ("H" with "R1"). Abort.
  Lemma test_before o R : |-- o |-> (R -* R).
  Proof. Fail iIntros "R". Abort.

  #[global] Instance into_wand_offsetR o p q R R1 R2 :
    IntoWand p q R R1 R2 → IntoWand p q (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /IntoWand -!_offsetR_intuitionistically_if.
    by rewrite -_offsetR_wand (into_wand p q R).
  Qed.
  #[global] Instance from_wand_offsetR o R R1 R2 :
    FromWand R R1 R2 → FromWand (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /FromWand. by rewrite -_offsetR_wand (from_wand R).
  Qed.

  Lemma test_after o R1 R2 : o |-> (R1 -* R2) |-- o |-> R1 -* o |-> R2.
  Proof. iIntros "H R1". iApply ("H" with "R1"). Abort.
  Lemma test_after o R : |-- o |-> (R -* R).
  Proof. iIntros "R". Abort.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R1.
  Proof. Fail by iIntros "[$ _]". Abort.
  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R2.
  Proof. Fail by iIntros "[_ $]". Abort.

  #[global] Instance into_and_offsetR p o R R1 R2 :
    IntoAnd p R R1 R2 → IntoAnd p (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /IntoAnd. rewrite -_offsetR_intuitionistically_if into_and.
    by rewrite _offsetR_intuitionistically_if _offsetR_and.
  Qed.

  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R1.
  Proof. by iIntros "[$ _]". Abort.
  Lemma test_before o R1 R2 : o |-> (R1 //\\ R2) |-- o |-> R2.
  Proof. by iIntros "[_ $]". Abort.

  (** Feed the [iSplit] tactic. *)
  Lemma test_before o R1 R2 : o |-> R1 //\\ o |-> R2 |-- o |-> (R1 //\\ R2).
  Proof. iIntros "H". Fail iSplit. Abort.

  #[global] Instance from_and_offsetR o R R1 R2 :
    FromAnd R R1 R2 → FromAnd (o |-> R) (o |-> R1) (o |-> R2).
  Proof.
    intros. rewrite /FromAnd. by rewrite -_offsetR_and (from_and R).
  Qed.

  Lemma test_after o R1 R2 : o |-> R1 //\\ o |-> R2 |-- o |-> (R1 //\\ R2).
  Proof. iIntros "H". iSplit. Abort.

  (** Feed the [iFrame] tactic. *)
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail iFrame "H1". Abort.
  Lemma test_before o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". Fail iFrame "H2". Abort.

  #[global] Instance frame_offsetR p o R R1 R2 :
    Frame p R R1 R2 →
    Frame p (o |-> R) (o |-> R1) (o |-> R2) | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite/Frame=><-. by rewrite -_offsetR_intuitionistically_if -_offsetR_sep.
  Qed.

  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". iFrame "H1". Abort.
  Lemma test_after o R1 R2 : o |-> R1 |-- o |-> R2 -* o |-> (R1 ** R2).
  Proof. iIntros "H1 H2". iFrame "H2". Abort.

  (** Framing between [P] and [_offsetR o (pureR P)]. *)

  Lemma test_before (p : ptr) o R : p |-> o |-> R |-- p ,, o |-> R.
  Proof. Fail by iIntros "$". Abort.
  #[global] Instance frame_at_offsetR_1 b (p : ptr) o R P (Q : mpred) :
    Frame b (p ,, o |-> R) P Q ->
    Frame b (p |-> o |-> R) P Q | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof. by rewrite/Frame _at_offsetR=>->. Qed.
  Lemma test_after (p : ptr) o R : p |-> o |-> R |-- p ,, o |-> R.
  Proof. by iIntros "$". Abort.

  (** TODO (PDS): Both the preceding and the following would make TC
      resolution diverge. [Hint Cut] might help, as might enabling the
      IPM's [monPred] framing instances to apply to [_at]. *)
  Section todo.
    Lemma test_before (p : ptr) o R : p ,, o |-> R |-- p |-> o |-> R.
    Proof. Fail by iIntros "$". Abort.
    (** TODO (proofmode): Given [p ,, o |-> R] we should be able to
        frame to get [p |-> o |-> R]. *)
    Lemma frame_at_offsetR_2 b (p : ptr) o R P (Q : mpred) :
      Frame b (p |-> o |-> R) P Q ->
      Frame b (p ,, o |-> R) P Q.
    Proof. by rewrite/Frame _at_offsetR=>->. Qed.
    Existing Instance frame_at_offsetR_2 | 2. (* Prio 2 to not shadow [frame_here]. *)
    Lemma test_after (p : ptr) o R : p ,, o |-> R |-- p |-> o |-> R.
    Proof. by iIntros "$". Abort.
  End todo.

  (** [IntoExist], [FromExist] *)
  Lemma test_before {A} o (R : A → Rep) :
    o |-> (Exists x, R x) |-- Exists x, o |-> R x.
  Proof. Fail iDestruct 1 as (x) "R". Abort.
  Lemma test_before {A} o (R : A → Rep) :
    Exists x, o |-> R x |-- o |-> (Exists x, R x).
  Proof. iDestruct 1 as (x) "R". Fail iExists x. Abort.

  #[global] Instance into_exist_offsetR {A} o R1 (R2 : A → Rep) name :
    IntoExist R1 R2 name → IntoExist (o |-> R1) (λ x, o |-> R2 x) name.
  Proof. intros H. by rewrite /IntoExist H _offsetR_exists. Qed.
  #[global] Instance from_exist_offsetR {A} o R1 (R2 : A → Rep) :
    FromExist R1 R2 → FromExist (o |-> R1) (λ x, o |-> R2 x).
  Proof. intros H. by rewrite/FromExist -H _offsetR_exists. Qed.

  Lemma test_after {A} o (R : A → Rep) :
    o |-> (Exists x, R x) |-- Exists x, o |-> R x.
  Proof. iDestruct 1 as (x) "R". Abort.
  Lemma test_after {A} o (R : A → Rep) :
    Exists x, o |-> R x |-- o |-> (Exists x, R x).
  Proof. iDestruct 1 as (x) "R". iExists x. Abort.

  (** [IntoForall], [FromForall] *)
  Lemma test_before {A} o (R : A → Rep) :
    o |-> (Forall x, R x) |-- Forall x, o |-> R x.
  Proof. iIntros "R" (x). Fail iSpecialize ("R" $! x). Abort.
  Lemma test_before {A} o (R : A → Rep) :
    Forall x, o |-> R x |-- o |-> Forall x, R x.
  Proof. Fail iIntros "R" (x). Abort.

  #[global] Instance into_forall_offsetR {A} o R1 (R2 : A → Rep) :
    IntoForall R1 R2 → IntoForall (o |-> R1) (λ x, o |-> R2 x).
  Proof. intros H. by rewrite /IntoForall H _offsetR_forall. Qed.
  #[global] Instance from_forall_offsetR {A} o R1 (R2 : A → Rep) name :
    FromForall R1 R2 name → FromForall (o |-> R1) (λ x, o |-> R2 x) name.
  Proof. intros H. by rewrite /FromForall -_offsetR_forall H. Qed.

  Lemma test_after {A} o (R : A → Rep) :
    o |-> (Forall x, R x) |-- Forall x, o |-> R x.
  Proof. iIntros "R" (x). iSpecialize ("R" $! x). Abort.
  Lemma test_after {A} o (R : A → Rep) :
    Forall x, o |-> R x |-- o |-> Forall x, R x.
  Proof. iIntros "R" (x). iApply "R". Abort.

  (* [FromPure] *)
  Lemma test_before {P : Prop} (o : offset) : |-- _offsetR o (bi_pure P).
  Proof. iIntros. Fail iPureIntro. Abort.

  #[global] Instance _offsetR_from_pure {a o R T} (H : FromPure a R T) : FromPure a (_offsetR o R) T.
  Proof. by red; red in H; rewrite -H _offsetR_affinely_if _offsetR_pure. Qed.

  Lemma test_after {P : Prop} (o : offset) : |-- _offsetR o (bi_pure P).
  Proof. iIntros. iPureIntro. Abort.

  (* [IntoPure] *)
  #[global] Instance _offsetR_into_pure {p} {P : Rep} {T} : IntoPure P T -> IntoPure (_offsetR p P) T.
  Proof. red; intros ->; by rewrite _offsetR_pure. Qed.

  Lemma test_after {P : Prop} (o : offset) : _offsetR o (bi_pure P) |-- True.
  Proof. iIntros "%". Abort.

  (* [IsExcept0] *)
  #[global] Instance is_except0_offsetR {R o} (H : IsExcept0 R) : IsExcept0 (_offsetR o R).
  Proof. red. by rewrite -_offsetR_except_0 H. Qed.

End _offsetR_instances.

(** * Instances for [pureR] *)
Section pureR_instances.
  Context `{Σ : cpp_logic}.
  Implicit Types R : Rep.
  Implicit Types P : mpred.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before P1 P2 : pureR (P1 ** P2) |-- pureR P1 ** pureR P2.
  Proof. Fail by iIntros "[$$]". Abort.

  #[global] Instance into_sep_pureR P P1 P2 :
    IntoSep P P1 P2 → IntoSep (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /IntoSep. by rewrite (into_sep P) pureR_sep.
  Qed.

  Lemma test_after P1 P2 : pureR (P1 ** P2) |-- pureR P1 ** pureR P2.
  Proof. by iIntros "[$$]". Abort.

  (** Feed the [iSplitL], [iSplitR], [iCombine] tactics. *)
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail by iSplitL "H1". Abort.
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail by iSplitR "H2". Abort.
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail by iCombine "H1 H2" as "H". Abort.

  #[global] Instance from_sep_pureR P P1 P2 :
    FromSep P P1 P2 → FromSep (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /FromSep. by rewrite -pureR_sep (from_sep P).
  Qed.

  #[global] Instance combine_sep_as_pureR P P1 P2 :
    CombineSepAs P1 P2 P → CombineSepAs (pureR P1) (pureR P2) (pureR P) | 10.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -pureR_sep H.
  Qed.

  (* [CombineSepAs] does not have a base instance for [bi_sep] (unlike [FromSep]. *)
  #[global] Instance combine_sep_as_pureR_base P1 P2 :
    CombineSepAs (pureR P1) (pureR P2) (pureR (P1 ** P2)) | 100.
  Proof.
    intros. rewrite /CombineSepAs. by rewrite -pureR_sep.
  Qed.

  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". by iSplitL "H1". Abort.
  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". by iSplitR "H2". Abort.
  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". by iCombine "H1 H2" as "H". Abort.

  (** [IntoWand], [FromWand] *)
  Lemma test_before P1 P2 : pureR (P1 -* P2) |-- pureR P1 -* pureR P2.
  Proof. iIntros "H P1". Fail iApply ("H" with "P1"). Abort.
  Lemma test_before P : |-- pureR (P -* P).
  Proof. Fail iIntros "P". Abort.

  #[global] Instance into_wand_pureR p q P P1 P2 :
    IntoWand p q P P1 P2 → IntoWand p q (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /IntoWand -!pureR_intuitionistically_if.
    by rewrite -pureR_wand (into_wand p q P).
  Qed.
  #[global] Instance from_wand_pureR P P1 P2 :
    FromWand P P1 P2 → FromWand (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /FromWand. by rewrite -pureR_wand (from_wand P).
  Qed.

  Lemma test_after P1 P2 : pureR (P1 -* P2) |-- pureR P1 -* pureR P2.
  Proof. iIntros "H P1". iApply ("H" with "P1"). Abort.
  Lemma test_after P : |-- pureR (P -* P).
  Proof. iIntros "P". Abort.

  (** Feed the introduction pattern ["[H1 H2]"]. *)
  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P1.
  Proof. Fail by iIntros "[$ _]". Abort.
  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P2.
  Proof. Fail by iIntros "[_ $]". Abort.

  #[global] Instance into_and_pureR p P P1 P2 :
    IntoAnd p P P1 P2 → IntoAnd p (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /IntoAnd. rewrite -pureR_intuitionistically_if into_and.
    by rewrite pureR_intuitionistically_if pureR_and.
  Qed.

  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P1.
  Proof. by iIntros "[$ _]". Abort.
  Lemma test_before P1 P2 : pureR (P1 //\\ P2) |-- pureR P2.
  Proof. by iIntros "[_ $]". Abort.

  (** Feed the [iSplit] tactic. *)
  Lemma test_before P1 P2 : pureR P1 //\\ pureR P2 |-- pureR (P1 //\\ P2).
  Proof. iIntros "H". Fail iSplit. Abort.

  #[global] Instance from_and_pureR P P1 P2 :
    FromAnd P P1 P2 → FromAnd (pureR P) (pureR P1) (pureR P2).
  Proof.
    intros. rewrite /FromAnd. by rewrite -pureR_and (from_and P).
  Qed.

  Lemma test_after P1 P2 : pureR P1 //\\ pureR P2 |-- pureR (P1 //\\ P2).
  Proof. iIntros "H". iSplit. Abort.

  (** Feed the [iFrame] tactic. *)
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail iFrame "H1". Abort.
  Lemma test_before P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". Fail iFrame "H2". Abort.

  #[global] Instance frame_pureR p P P1 P2 :
    Frame p P P1 P2 →
    Frame p (pureR P) (pureR P1) (pureR P2) | 2. (* Prio 2 to not shadow [frame_here]. *)
  Proof.
    rewrite/Frame=><-. by rewrite -pureR_intuitionistically_if -pureR_sep.
  Qed.

  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". iFrame "H1". Abort.
  Lemma test_after P1 P2 : pureR P1 |-- pureR P2 -* pureR (P1 ** P2).
  Proof. iIntros "H1 H2". iFrame "H2". Abort.

  (** [IntoExist], [FromExist] *)
  Lemma test_before {A} (P : A → mpred) :
    pureR (Exists x, P x) |-- Exists x, pureR (P x).
  Proof. Fail iDestruct 1 as (x) "P". Abort.
  Lemma test_before {A} (P : A → mpred) :
    Exists x, pureR (P x) |-- pureR (Exists x, P x).
  Proof. iDestruct 1 as (x) "P". Fail iExists x. Abort.

  #[global] Instance into_exist_pureR {A} P1 (P2 : A → mpred) name :
    IntoExist P1 P2 name → IntoExist (pureR P1) (λ x, pureR (P2 x)) name.
  Proof. intros H. by rewrite /IntoExist H pureR_exist. Qed.
  #[global] Instance from_exist_pureR {A} P1 (P2 : A → mpred) :
    FromExist P1 P2 → FromExist (pureR P1) (λ x, pureR (P2 x)).
  Proof. intros H. by rewrite/FromExist -H pureR_exist. Qed.

  Lemma test_after {A} (P : A → mpred) :
    pureR (Exists x, P x) |-- Exists x, pureR (P x).
  Proof. iDestruct 1 as (x) "P". Abort.
  Lemma test_after {A} (P : A → mpred) :
    Exists x, pureR (P x) |-- pureR (Exists x, P x).
  Proof. iDestruct 1 as (x) "P". iExists x. Abort.

  (** [IntoForall], [FromForall] *)
  Lemma test_before {A} (P : A → mpred) :
    pureR (Forall x, P x) |-- Forall x, pureR (P x).
  Proof. iIntros "P" (x). Fail iSpecialize ("P" $! x). Abort.
  Lemma test_before {A} (P : A → mpred) :
    Forall x, pureR (P x) |-- pureR (Forall x, P x).
  Proof. Fail iIntros "P" (x). Abort.

  #[global] Instance into_forall_pureR {A} P1 (P2 : A → mpred) :
    IntoForall P1 P2 → IntoForall (pureR P1) (λ x, pureR (P2 x)).
  Proof. intros H. by rewrite /IntoForall H pureR_forall. Qed.
  #[global] Instance from_forall_pureR {A} P1 (P2 : A → mpred) name :
    FromForall P1 P2 name → FromForall (pureR P1) (λ x, pureR (P2 x)) name.
  Proof. intros H. by rewrite /FromForall -pureR_forall H. Qed.

  Lemma test_after {A} (P : A → mpred) :
    pureR (Forall x, P x) |-- Forall x, pureR (P x).
  Proof. iIntros "P" (x). iSpecialize ("P" $! x). Abort.
  Lemma test_after {A} (P : A → mpred) :
    Forall x, pureR (P x) |-- pureR (Forall x, P x).
  Proof. iIntros "P" (x). iApply "P". Abort.

  (** Feeding the [iInv] tactic to open invariants written [pureR Inv]
  or [offset |-> pureR Inv] doesn't currently seem possible. The
  generality of the proof mode's [IntoAcc] and [accessor] wrt
  arbitrary modalities doesn't work well with [monPred]. We can
  specialize those to fancy updates (which covers all
  invariant-related [IntoAcc] instances in Iris), but a problem
  remains. The underlying lemma [coq_tactics.tac_inv_elim] generates
  an entailment involving [monPred] that the tactic [iInv] seems
  unable to handle. *)

  #[global] Instance is_except0_pureR {P} (H : IsExcept0 P) : IsExcept0 (pureR P).
  Proof.
    red. red in H. apply Rep_entails_at => p.
      by rewrite !_at_pureR !_at_except_0 !_at_pureR.
  Qed.

  Lemma test_before {P : Prop} (p : ptr) : p |-> pureR (bi_pure P) |-- True.
  Proof. Fail iIntros "%". Abort.

  #[global] Instance into_pure_pureR {P T} (H : IntoPure P T) : IntoPure (pureR P) T.
  Proof. red. apply Rep_entails_at => p. by rewrite H !_at_pure _at_pureR. Qed.

  Lemma test_after {P : Prop} (p : ptr) : p |-> pureR (bi_pure P) |-- True.
  Proof. iIntros "%". Abort.

  (* [FromPure] *)
  Lemma test_before {P : Prop} (p : ptr) : |-- p |-> pureR (bi_pure P).
  Proof. iIntros. Fail iPureIntro. Abort.

  #[global] Instance from_pure_pureR {a P T} (H : FromPure a P T) : FromPure a (pureR P) T.
  Proof.
    apply Rep_entails_at => p. by rewrite _at_affinely_if _at_pure _at_pureR.
  Qed.

  Lemma test_after {P : Prop} (p : ptr) : |-- p |-> pureR (bi_pure P).
  Proof. iIntros. iPureIntro. Abort.

End pureR_instances.
