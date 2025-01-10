(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(** Definitions for the semantics
 *)
Require Import bedrock.prelude.base.

Require Import stdpp.coPset.
Require Import iris.bi.monpred.
Require Import bedrock.lang.proofmode.proofmode.
Require Import iris.proofmode.classes.

Require Import bedrock.lang.cpp.syntax.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.pred.
Require Import bedrock.lang.cpp.logic.heap_pred.
Require Import bedrock.lang.cpp.logic.translation_unit.
Require Import bedrock.lang.cpp.logic.free_temps.
Require Import bedrock.lang.bi.errors.

#[local] Set Primitive Projections.

Require bedrock.lang.bi.linearity.

(* continuations
 * C++ statements can terminate in 4 ways.
 *
 * note(gmm): technically, they can also raise exceptions; however,
 * our current semantics doesn't capture this. if we want to support
 * exceptions, we should be able to add another case,
 * `k_throw : val -> mpred`.
 *)
Variant ReturnType {T : Type} : Type :=
| Normal (_ : T)
| Break
| Continue
| ReturnVal (_ : ptr)
| ReturnVoid
.
#[global] Arguments ReturnType _ : clear implicits.
#[global] Instance ReturnType_inh {T} : Inhabited (ReturnType T).
Proof. constructor; apply Break. Qed.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  Import linearity.
  #[local] Opaque FreeTemps.canon.

  (* The type of the continuation *)
  #[local] Definition K : Type :=
    forall free : FreeTemps.t, FreeTemps.IsCanonical free -> mpred.

  #[local]
  Lemma K_entails (K : K)
    free1 free2 pf1 pf2 :
    free1 ≡ free2 -> K free1 pf1 |-- K free2 pf2.
  Proof. intros. rewrite FreeTemps.K_ext; eauto. Qed.

  (* the monad for expression evaluation *)
  Record M {t : Type} := mk
    { _wp : (t -> K) -> mpred
    ; _frame : forall K1 K2, (Forall x free pf, K1 x free pf -* K2 x free pf) |-- _wp K1 -* _wp K2
    ; _ne : forall K1 K2 n, (forall x y z, K1 x y z ≡{n}≡ K2 x y z) -> _wp K1 ≡{n}≡ _wp K2 }.
  #[global] Arguments M _ : clear implicits.
  #[local] Coercion _wp : M >-> Funclass.

  (* The monad used for evaluating C++ code.
     It supports control flow such as <<break>>, <<continue>>, and <<return>>
   *)
  Definition Mlocal T := M (ReturnType T).

  (* The global monad used for functions.
     NOTE: this actually does not need [FreeTemps.t]
   *)
  Definition Mglobal T := M T.

  (* The canonical notion of equivalence on [M _] *)
  #[global] Instance M_equiv [T] : Equiv (M T) :=
    fun a b => forall K1 K2, (forall x y z, K1 x y z ⊣⊢ K2 x y z) -> a K1 ⊣⊢ b K2.
  #[global] Instance M_equiv_refl {T} : Reflexive (≡@{M T}).
  Proof.
    repeat red. intros.
    split'.
    { iApply _frame; iIntros (???). rewrite H; eauto. }
    { iApply _frame; iIntros (???). rewrite H; eauto. }
  Qed.
  #[global] Instance M_equiv_sym {T} : Symmetric (≡@{M T}).
  Proof.
    do 3 red; simpl; intros. symmetry; apply H.
    intros; symmetry. apply H0.
  Qed.
  #[global] Instance M_equiv_trans {T} : Transitive (≡@{M T}).
  Proof.
    repeat intro; simpl. etrans. eapply H. eapply H1.
    eapply H0. intros. reflexivity.
  Qed.

  (* The canonical notation of approximation/entailment
     Effectively, [a ⊆ b] if all behaviors of [a] are included in [b].
   *)
  #[global] Instance M_subseteq {T} : SubsetEq (M T) :=
    fun a b =>
      forall K1 K2, (forall x y z, K1 x y z ⊢ K2 x y z) -> a K1 ⊢ b K2.
  #[global] Instance M_subseteq_refl {T} : Reflexive (⊆@{M T}).
  Proof. repeat intro. iApply _frame; iIntros (???); iApply H. Qed.
  #[global] Instance M_subseteq_trans {T} : Transitive (⊆@{M T}).
  Proof.
    repeat intro. etrans.
    { iApply H. reflexivity. }
    { iApply H0. apply H1. }
  Qed.

  (** The distance metric on [M].
   *)
  #[global] Instance M_Dist {T} : Dist (M T) :=
    fun n (a b : M T) =>
      forall K1 K2, (forall x y z, K1 x y z ≡{n}≡ K2 x y z) -> a K1 ≡{n}≡ b K2.

  (** ** Monad Operators *)

  #[global] Instance ReturnType_fmap : FMap ReturnType :=
    fun _ _ f x => match x with
                | Normal x => Normal (f x)
                | Break => Break
                | Continue => Continue
                | ReturnVoid => ReturnVoid
                | ReturnVal p => ReturnVal p
                end.

  #[global,program]
  Instance Mlocal_ret : MRet Mlocal :=
    fun _ v => {| _wp K := K (Normal v) FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X"; iApply "X".
  Qed.
  Next Obligation.
    simpl; intros. apply H.
  Qed.
  #[global,program]
  Instance Mlocal_map : FMap Mlocal :=
    fun _ _ f m => {| _wp K := m.(_wp) (fun t => K (f <$> t)) |}.
  Next Obligation.
    intros; simpl.
    iIntros "X"; iApply _frame.
    iIntros (??); iApply "X".
  Qed.
  Next Obligation.
    simpl; intros. apply _ne; eauto.
  Qed.
  #[global,program]
  Instance Mlocal_bind : MBind Mlocal :=
    fun _ _ k c =>
      {| _wp K := c (fun v f _ => match v with
                               | Normal v => k v (fun v' f' _ => K v' (FreeTemps.canon $ f' >*> f)%free _)
                               | Break => K Break f _
                               | Continue => K Continue f _
                               | ReturnVal p => K (ReturnVal p) f _
                               | ReturnVoid => K ReturnVoid f _
                               end) |}.
  Next Obligation.
    simpl; intros. iIntros "K"; iApply _frame.
    iIntros (???). case_match; try iApply _frame; eauto.
    iIntros (???); iApply "K".
  Qed.
  Next Obligation.
    simpl; intros.
    apply _ne; intros. case_match; eauto. apply _ne; simpl; intros; apply H.
  Qed.

  #[global,program]
  Instance M_ret : MRet M :=
    fun _ v => {| _wp K := K v FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X"; iApply "X".
  Qed.
  Next Obligation.
    simpl; intros. apply H.
  Qed.

  #[global,program]
  Instance M_map : FMap M :=
    fun _ _ f m => {| _wp K := m.(_wp) (fun t => K (f t)) |}.
  Next Obligation.
    intros; simpl.
    iIntros "X"; iApply _frame.
    iIntros (??); iApply "X".
  Qed.
  Next Obligation.
    simpl; intros. apply _ne; eauto.
  Qed.

  (* Question: Should we implement [ap]? *)

  #[global,program]
  Instance M_bind : MBind M :=
    fun _ _ k c =>
      {| _wp K := c (fun v f _ => k v (fun v' f' _ => K v' (FreeTemps.canon $ f' >*> f)%free _)) |}.
  Next Obligation.
    simpl; intros. iIntros "K"; iApply _frame.
    iIntros (???). iApply _frame. iIntros (???); iApply "K".
  Qed.
  Next Obligation.
    simpl; intros. apply _ne; intros. apply _ne; intros. apply H.
  Qed.

  (**  These operations actually form a monad *)
  Lemma mret_mbind {T U} v (k : T -> M U) : mbind k (mret v) ≡ k v.
  Proof.
    red. rewrite /M_equiv/M_bind/M_ret/=. red. simpl; intros.
    split'.
    { iApply _frame; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails.
      by rewrite FreeTemps.canon_equiv FreeTemps.seq_id_unitR. }
    { iApply _frame; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails.
      by rewrite FreeTemps.canon_equiv FreeTemps.seq_id_unitR. }
  Qed.

  Lemma mbind_mret {T} (m : M T) : mbind mret m ≡ m.
  Proof.
    red; rewrite /M_equiv/M_bind/M_ret; red; simpl; intros.
    split'.
    { iApply _frame; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails. rewrite FreeTemps.canon_equiv FreeTemps.seq_left_id; eauto. }
    { iApply _frame; iIntros (???) "?"; iStopProof.
      rewrite H; apply K_entails; rewrite FreeTemps.canon_equiv FreeTemps.seq_left_id; eauto. }
  Qed.

  Lemma mbind_mbind {T U V} (m : M T) (k1 : T -> M U) (k2 : U -> M V) :
    mbind (fun x => mbind k2 (k1 x)) m ≡ mbind k2 (mbind k1 m).
  Proof.
    red; rewrite /M_equiv/M_bind; red; simpl; intros.
    split';
      iApply _frame; iIntros (???); iApply _frame; iIntros (???); iApply _frame; iIntros (???);
      rewrite H; eauto; iIntros; iStopProof; apply K_entails.
    all: rewrite !FreeTemps.canon_equiv FreeTemps.seq_assoc; eauto.
  Qed.

  (** Conversions between the monads *)
  Definition M2local {T} (m : Mglobal T) : Mlocal T :=
    Normal <$> m.

  (** The interpreter for the monad.

      TODO: confirm whether this is necessary, or make it a notation. This is essentially the compatibility constant
            for [_wp], but some of the typeclass search didn't seem to work correctly with the constant

      TODO: it would be nice to hide the canonicity proof because it is an implementation detail of the monad, but
            that break [by_WP].
   *)
  Definition WP {T} (m : M T) := _wp m.
(*
  Definition WP {T} (m : M T) (Q : T -> FreeTemps.t -> mpred) : mpred :=
    m (fun x f _ => Q x f).
 *)

  Definition Knormal {T U} (k : T -> M U) (Q : U -> K) : T -> K :=
    fun t free _ => k t (fun u free' _ => Q u (FreeTemps.canon (free' >*> free)) _).

  Lemma WP_Mbind {T U} (m : M T) (k : T -> M U) Q :
    WP m (Knormal k Q) -|- WP (mbind k m) Q.
  Proof.
    rewrite /M_bind/WP/Knormal/=.
    iSplit; iApply _frame; iIntros (???); eauto.
  Qed.

  Lemma WP_ret {T} (v : T) Q :
    Q v FreeTemps.id _ -|- WP (mret v) Q.
  Proof. by rewrite /WP/M_ret/=. Qed.

  (** ** The Effects of the Monad

      These currently follow the "operational logic" style used by tools
      such as Viper, but these could possibly be re-phrased in an
      operational but non-logical setup.

      Purely logical features such as fancy updates do not fit naturally
      into this setup.
   *)

  #[program]
  Definition Mproduce (P : mpred) : M unit :=
    {| _wp := fun K => P -* K () FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X Y P". iApply "X". iApply "Y". iApply "P".
  Qed.
  Next Obligation.
    simpl; intros. f_equiv. apply H.
  Qed.
  #[program]
  Definition Mconsume (P : mpred) : M unit :=
    {| _wp := fun K => P ** K () FreeTemps.id _ |}.
  Next Obligation.
    intros; simpl. iIntros "X [$ K]". iApply "X". iApply "K".
  Qed.
  Next Obligation.
    simpl; intros. f_equiv. apply H.
  Qed.

  Lemma WP_produce P Q :
    P -* Q () FreeTemps.id _ |-- WP (Mproduce P) Q.
  Proof. reflexivity. Qed.
  Lemma WP_consume P Q :
    P ** Q () FreeTemps.id _ |-- WP (Mconsume P) Q.
  Proof. reflexivity. Qed.

  Definition Massume (P : Prop) : M unit := Mproduce [| P |].
  Definition Mrequire (P : Prop) : M unit := Mconsume [| P |].

  #[program]
  Definition Mnd (t : Type) : M t :=
    {| _wp K := ∀ x : t, K x FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros.
    iIntros "K X" (?); iApply "K"; eauto.
  Qed.
  Next Obligation.
    simpl; intros. f_equiv; intro; eauto.
  Qed.
  #[program]
  Definition Mangelic (t : Type) : M t :=
    {| _wp K := ∃ x : t, K x FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros.
    iIntros "K X"; iDestruct "X" as (?) "X"; iExists _; iApply "K"; eauto.
  Qed.
  Next Obligation.
    simpl; intros. f_equiv; intro; eauto.
  Qed.

  #[program]
  Definition Mub {t : Type} : M t :=
    {| _wp _ := False%I |}.
  Next Obligation. simpl; intros. iIntros "? []". Qed.
  Next Obligation. simpl; intros. done. Qed.
  #[program]
  Definition Many {t : Type} : M t :=
    {| _wp _ := True%I |}.
  Next Obligation. simpl; intros; iIntros "? ?". iApply bi.pure_intro; [ trivial | ]. iStopProof. reflexivity. Qed.
  Next Obligation. simpl; intros. done. Qed.

  #[program]
  Definition Merror {t : Type} {ERR : Type} (err : ERR) : M t :=
    {| _wp _ := ERROR err |}.
  Next Obligation. simpl; intros. rewrite ERROR_False. iIntros "? []". Qed.
  Next Obligation. simpl; intros. done. Qed.

  #[program]
  Definition Munsupported {t : Type} {ERR : Type} (err : ERR) : M t :=
    {| _wp _ := ERROR err |}.
  Next Obligation. simpl; intros. rewrite ERROR_False. iIntros "? []". Qed.
  Next Obligation. simpl; intros. done. Qed.

  #[program]
  Definition Mpush_free (f : FreeTemps.t) : Mlocal () :=
    {| _wp K := K (Normal ()) (FreeTemps.canon f) _ |}.
  Next Obligation. simpl; intros. iIntros "K"; iApply "K". Qed.
  Next Obligation. simpl; intros. done. Qed.

  #[program]
  Definition Matomically {t} (m : M t) : M t :=
    {| _wp K := |={top,∅}=> m.(_wp) (fun r free _ => |={∅,top}=> K r free _) |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X".
    iApply _frame. iIntros (???) ">X !>"; iRevert "X"; iApply "K".
  Qed.
  Next Obligation. simpl; intros. f_equiv. apply _ne; intros. f_equiv. eauto. Qed.

  #[program]
  Definition Mnon_atomically {t} (m : M t) : M t :=
    {| _wp K := |={top}=> m.(_wp) (fun r free _ => |={top}=> K r free _) |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X".
    iApply _frame. iIntros (???) ">X !>"; iRevert "X"; iApply "K".
  Qed.
  Next Obligation. simpl; intros. f_equiv. apply _ne; intros. f_equiv. eauto. Qed.

  #[program]
  Definition Mfupd (E1 E2 : coPset): M unit :=
    {| _wp K := |={E1,E2}=> K () FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X"; iApply "K".
  Qed.
  Next Obligation. simpl; intros. f_equiv. eauto. Qed.

  #[program]
  Definition Mstable : M unit :=
    {| _wp K := |={top}=> K () FreeTemps.id _ |}%I.
  Next Obligation.
    simpl; intros. iIntros "K >X !>"; iRevert "X"; iApply "K".
  Qed.
  Next Obligation. simpl; intros. f_equiv. eauto. Qed.

  #[program]
  Definition Mboth {t} (a b : M t) : M t :=
    {| _wp K := a K //\\ b K |}.
  Next Obligation.
    simpl; intros. iIntros "K X".
    iSplit; [ iDestruct "X" as "[X _]" | iDestruct "X" as "[_ X]" ]; iRevert "X"; iApply _frame; iIntros (??); iApply "K".
  Qed.
  Next Obligation. simpl; intros. f_equiv; apply _ne; eauto. Qed.

  Definition Mas {T U} (inj : T -> U) (v : U) : M T :=
    letM* p := Mangelic _ in
    letM* '() := Mrequire (v = inj p) in
    mret p.

  (*
  Definition Mread {t} (R : t -> mpred) : M t :=
    MonPred (I:=M_index t) (fun K => Exists v, R v ** (R v -* K v FreeTemps.id)) _.
  Definition Mread_with {TT : tele} (R : TT -t> mpred) : M TT :=
    MonPred (I:=M_index TT) (fun K => ∃.. v, tele_app R v ** (tele_app R v -* K v FreeTemps.id))%I _.
   *)

  (** TODO: Probably better as a [Notation] *)
  Definition Frame {T} (a b : M T) : Prop :=
    forall Q Q', (Forall x y z, Q x y z -* Q' x y z) ⊢ a Q -* b Q'.
  Definition FrameWith {T} (P : T -> mpred) (a b : M T) : Prop :=
    forall Q Q', (Forall x y z, P x -* Q x y z -* Q' x y z) ⊢ a Q -* b Q'.

  Definition FrameI {T} (a b : M T) : mpred :=
    Forall Q Q', (Forall x y z, Q x y z -* Q' x y z) -* a Q -* b Q'.
  Definition FrameWithI {T} (P : T -> mpred) (a b : M T) : mpred :=
    Forall Q Q', (Forall x y z, P x -* Q x y z -* Q' x y z) -* a Q -* b Q'.

  Instance fmap_proper {T U} : Proper (pointwise_relation _ (=) ==> (≡@{M T}) ==> (≡@{M U})) fmap.
  Proof.
    repeat intro; rewrite /fmap/=.
    apply H0.  intros. rewrite H. apply H1.
  Qed.

  Lemma Mmap_frame_strong {T U} c1 c2 (f : T -> U) :
    FrameI c1 c2
    |-- Forall Q Q', (Forall x y pf, Q (f x) y pf -* Q' (f x) y pf) -* _wp (f <$> c1) Q -* _wp (f <$> c2) Q'.
  Proof.
    rewrite /FrameI/M_map; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.

  Lemma Mmap_frame {T U} c1 c2 (f : T -> U) :
    FrameI c1 c2 |-- FrameI (f <$> c1) (f <$> c2).
  Proof.
    rewrite /FrameI/M_map; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.

  Lemma Mbind_frame {T U} c1 c2 (k1 k2 : T -> M U) :
    FrameI c1 c2 |-- (Forall x, FrameI (k1 x) (k2 x)) -* FrameI (mbind k1 c1) (mbind k2 c2).
  Proof.
    rewrite /FrameI/M_bind; iIntros "A B" (??) "C".
    iApply "A". iIntros (???). iApply "B".
    iIntros (???); iApply "C".
  Qed.

  (** *** Indeterminately sequenced computations
      Note that [FreeTemps.t] is sequenced in reverse order of construction
      to encode the stack discipline guaranteed by C++.
      (CITATION NEEDED)
   *)
  #[program]
  Definition nd_seq {T U} (wp1 : Mlocal T) (wp2 : Mlocal U) : Mlocal (T * U) :=
    Mboth (letM* v1 := wp1 in
           letM* v2 := wp2 in
           mret (v1,v2))
          (letM* v2 := wp2 in
           letM* v1 := wp1 in
           mret (v1,v2)).

  Instance affinely_intowand {PROP : bi} (R P Q : PROP) : IntoWand false false R P Q -> IntoWand false false (<affine> R) P Q.
  Proof.
    rewrite /IntoWand/=.
    intros. rewrite H. rewrite bi.affinely_elim. done.
  Qed.


  Lemma nd_seq_frame {T U} wp1 wp2 :
    <affine> FrameI wp1 wp1 |-- <affine> FrameI wp2 wp2 -* FrameI (@nd_seq T U wp1 wp2) (nd_seq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    iSplit; [ iDestruct "D" as "[D _]" | iDestruct "D" as "[_ D]" ]; iRevert "D".
    { iApply "A". iIntros (???).
      case_match; eauto. iApply "B"; iIntros (???); case_match; eauto. }
    { iApply "B". iIntros (???).
      case_match; eauto. iApply "A"; iIntros (???); case_match; eauto. }
  Qed.

  (* Lifting non-deterministic sequencing to lists.

     NOTE: this is like the semantics of argument evaluation in C++.
   *)
  Fixpoint nd_seqs' {T} (f : nat) (qs : list (Mlocal T)) {struct f} : Mlocal (list T) :=
    match qs with
    | nil => mret nil
    | _ :: _ =>
      match f with
      | 0 => Mub
      | S f =>
        letM* '(pre, post, q) := M2local $ Mnd (list (Mlocal T) * list (Mlocal T) * Mlocal T) in
        letM* '() := M2local $ Mrequire (qs = pre ++ q :: post) in
        let lpre := length pre in
        q ≫= (fun t => (fun ts : list T => firstn lpre ts ++ t :: skipn lpre ts) <$> (nd_seqs' f (pre ++ post)))
      end
    end.

  Definition nd_seqs {T} (qs : list (Mlocal T)) : Mlocal (list T) := @nd_seqs' T (length qs) qs.

  Definition on_normal {T} (P : T -> Prop) (rt : ReturnType T) : Prop :=
    match rt with
    | Normal v => P v
    | _ => True
    end.
  Definition on_normalI {T} (P : T -> mpred) (rt : ReturnType T) : mpred :=
    match rt with
    | Normal v => P v
    | _ => emp
    end.

  Lemma nd_seqs'_frame_strong {T} n : forall (ls : list (Mlocal T)),
      n = length ls ->
      FrameWith (on_normalI $ fun x => [| length x = length ls |]) (nd_seqs' n ls) (nd_seqs' n ls).
  Proof.
    induction n; simpl; intros.
    { case_match; eauto.
      subst. simpl.
      iIntros (??) "X". iApply "X". eauto.
      iIntros (??) "? []". }
    { destruct ls. exfalso; simpl in *; congruence.
      inversion H.
      iIntros (??) "X Y". iIntros ([[pre post] q]) => /=.
      iDestruct ("Y" $! (pre,post,q)) as "[% Y]"=> /=; iFrame "%".
      iRevert "Y"; iApply _frame; iIntros (???).
      case_match; try iApply "X"; eauto.
      unfold FrameWith in IHn.
      specialize (IHn (pre ++ post)).
      subst.
      generalize (f_equal length H0) => /=; rewrite !length_app/= => ?.
      iApply IHn.
      { rewrite length_app; lia. }
      rewrite /on_normalI.
      iIntros ([] ??) "P"; simpl; iApply "X"; eauto.
      rewrite !length_app/=. iDestruct "P" as "%".
      iPureIntro.
      rewrite firstn_length_le; last lia.
      rewrite length_skipn. lia. }
  Qed.

  (*
  Lemma nd_seqs'_frame_strong {T} n : forall (ls : list (M T)) Q Q',
      n = length ls ->
      Forall x y, [| length x = length ls |] -* Q x y -* Q' x y
      |-- ([∗list] m ∈ ls, FrameI m m) -*
          nd_seqs' n ls Q -* nd_seqs' n ls Q'.
  Proof.
    induction n; simpl; intros.
    { case_match; eauto.
      subst. simpl.
      iIntros "X _". iApply "X". eauto. }
    { destruct ls. exfalso; simpl in *; congruence.
      inversion H.
      iIntros "X LS Y" (???) "%P".
      iSpecialize ("Y" $! pre).
      iSpecialize ("Y" $! post).
      iSpecialize ("Y" $! q).
      iDestruct ("Y" with "[]") as "Y"; first eauto.
      rewrite P.
      iDestruct "LS" as "(a&b&c)".
      iRevert "Y". rewrite /Mbind.
      iApply "b".
      iIntros (??).
      rewrite /Mmap.
      subst.
      assert (length ls = length (pre ++ post)).
      { have: (length (m :: ls) = length (pre ++ q :: post)) by rewrite P.
        rewrite !length_app /=. lia. }
      iDestruct (IHn with "[X]") as "X". eassumption.
      2:{
      iDestruct ("X" with "[a c]") as "X".
      iSplitL "a"; eauto.
      iApply "X". }
      simpl. iIntros (??) "%". iApply "X".
      revert H0 H1. rewrite !length_app/=.
      intros. iPureIntro.
      rewrite firstn_length_le; last lia.
      rewrite length_skipn. lia. }
  Qed.

  Lemma nd_seqs'_frame {T} n : forall (ls : list (M T)),
      n = length ls ->
      ([∗list] m ∈ ls, FrameI m m)
      |-- FrameI (nd_seqs' n ls) (nd_seqs' n ls).
  Proof.
    induction n; simpl; intros.
    { case_match.
      { subst. simpl.
        iIntros "_" (??) "X". iApply "X". }
      { iIntros "?" (??) "? []". } }
    { destruct ls. exfalso; simpl in *; congruence.
      inversion H.
      iIntros "LS" (??) "X Y"; iIntros (???) "%P".
      iSpecialize ("Y" $! pre).
      iSpecialize ("Y" $! post).
      iSpecialize ("Y" $! q).
      iDestruct ("Y" with "[]") as "Y"; first eauto.
      rewrite P.
      iDestruct "LS" as "(a&b&c)".
      iRevert "Y".
      iApply (Mbind_frame with "b [a c]"); eauto.
      iIntros (?).
      iApply Mmap_frame.
      rewrite -H1.
      iApply IHn.
      { have: (length (m :: ls) = length (pre ++ q :: post)) by rewrite P.
        rewrite !length_app /=. lia. }
      iSplitL "a"; eauto. }
  Qed.
  *)
  Lemma nd_seqs_frame_strong : forall {T} (ms : list (_ T)),
      FrameWith (on_normalI (fun x => [| length x = length ms |])) (nd_seqs ms) (nd_seqs ms).
  Proof.
    intros; iIntros (??) "K". iApply nd_seqs'_frame_strong; eauto.
  Qed.
  Lemma nd_seqs_frame : forall {T} (ms : list (_ T)),
      Frame (nd_seqs ms) (nd_seqs ms).
  Proof.
    intros; iIntros (??) "K". iApply nd_seqs_frame_strong; eauto.
    iIntros (???) "P".
    destruct x; simpl; iApply "K".
  Qed.

  (*
  (* sanity check on [nd_seq] and [nd_seqs] *)
  Example nd_seq_example : forall {T} (a b : M T),
      Proper (Mrel _) a -> Proper (Mrel _) b ->
      Mequiv _ (nd_seqs [a;b]) (Mmap (fun '(a,b) => [a;b]) $ nd_seq a b).
  Proof.
    rewrite /nd_seqs/=; intros.
    rewrite /Mmap/nd_seq.
    repeat intro.
    iSplit.
    { iIntros "X".
      iSplit.
      { iSpecialize ("X" $! nil [b] a eq_refl).
        iRevert "X".
        iApply H. repeat intro; simpl.
        iIntros "X".
        iSpecialize ("X" $! nil nil b eq_refl).
        iRevert "X".
        iApply H0. repeat intro; simpl.
        rewrite /Mret.
        rewrite (H1 _ _ _) => //. by rewrite FreeTemps.seq_id_unitL. }
      { iSpecialize ("X" $! [a] nil b eq_refl).
        iRevert "X". iApply H0. repeat intro; simpl.
        iIntros "X".
        iSpecialize ("X" $! nil nil a eq_refl).
        iRevert "X".
        iApply H. repeat intro; simpl.
        rewrite /Mret.
        rewrite H1 => //. by rewrite FreeTemps.seq_id_unitL. } }
    { iIntros "X" (pre post m Horder).
      destruct pre.
      { inversion Horder; subst.
        iDestruct "X" as "[X _]".
        rewrite /Mbind. iApply H; last iAssumption.
        iIntros (??) => /=.
        iIntros "X" (pre' post' m' Horder').
        assert (pre' = [] /\ m' = b /\ post' = []) as [?[??]]; last subst.
        { clear - Horder'.
          destruct pre'.
          - inversion Horder'; subst; auto.
          - destruct pre'; inversion Horder'. }
        iApply H0; last iAssumption.
        iIntros (??) => /=; rewrite /Mret/=.
        rewrite H1 => //. by rewrite FreeTemps.seq_id_unitL. }
      { assert (a = m0 /\ b = m /\ pre = [] /\ post = []) as [?[?[??]]]; last subst.
        { clear -Horder.
          inversion Horder; subst.
          destruct pre; inversion H1; subst; eauto.
          destruct pre; inversion H2. }
        iDestruct "X" as "[_ X]".
        rewrite /Mbind. iApply H0; last iAssumption.
        iIntros (??) "H" => /=. iIntros (pre' post' m' Horder')=> /=.
        assert (m0 = m' /\ pre' = [] /\ post' = []) as [?[??]]; last subst.
        { destruct pre'; inversion Horder'; subst; eauto.
          destruct pre'; inversion H4. }
        iApply H; last iAssumption.
        iIntros (??). rewrite /=/Mret/=.
        rewrite H1 => //.
        by rewrite FreeTemps.seq_id_unitL. } }
  Qed.
  *)

  (** *** sequencing of monadic compuations *)
  Definition Mseq {T U} (wp1 : Mlocal T) (wp2 : Mlocal U) : Mlocal (T * U) :=
    letM* v := wp1 in
    (fun x => (v,x)) <$> wp2.

  Lemma Mseq_frame {T U} wp1 wp1' wp2 wp2' :
    FrameI wp1 wp1' |-- <affine> FrameI wp2 wp2' -* FrameI (@Mseq T U wp1 wp2) (Mseq wp1' wp2').
  Proof.
    iIntros "A B" (??) "C".
    rewrite /Mseq/M_bind/=.
    iApply "A"; iIntros (???); case_match; eauto.
    iApply "B"; iIntros (???). iApply "C".
  Qed.

  (** [seqs es] is sequential evaluation of [es] *)
  Fixpoint seqs {T} (es : list (Mlocal T)) : Mlocal (list T) :=
    match es with
    | nil => mret []
    | e :: es => (fun '(a,b) => a :: b) <$> Mseq e (seqs es)
    end.

  Lemma seqs_frame_strong {T} : forall (ls : list (Mlocal T)) Q Q',
      ([∗list] m ∈ ls, <affine> FrameI m m)%I
      |-- (Forall x y pf, on_normalI (fun x => [| length x = length ls |]) x -* Q x y pf -* Q' x y pf) -*
          (seqs ls Q) -* (seqs ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "_ X"; iApply "X"; eauto.
    - iIntros "[A AS] K".
      rewrite /M_bind. iApply "A".
      iIntros (???).
      case_match; try iApply "K"; eauto.
      { iApply (IHls with "AS"); rewrite /on_normalI/=.
        iIntros ([]??) "P"; iApply "K"; eauto.
        iDestruct "P" as "%"; iPureIntro; simpl; eauto. }
  Qed.

  (*
  (** *** interleaving of monadic values

      We encode interleaving through concurrency which we represent through
      separable resources.

      NOTE: this is like the semantics of argument evaluation in C
   *)
  #[program]
  Definition Mpar {T U} (wp1 : M T) (wp2 : Mlocal U) : M (T * U) :=
    {| _wp K := Exists Q1 Q2, wp1 Q1 ** wp2 Q2 ** (Forall v1 v2 f1 f2 pf1 pf2, Q1 v1 f1 pf1 -* Q2 v2 f2 pf2 -* K (v1,v2) (FreeTemps.canon (f1 |*| f2)) _) |}.
  Next Obligation.
    simpl; intros.
    iIntros "K X". iDestruct "X" as (??) "[? [? Q]]".
    iExists Q1, Q2; iFrame. iIntros (??????) "Q1 Q2". iApply "K". iApply ("Q" with "Q1 Q2").
  Qed.

  Lemma Mpar_frame {T U} wp1 wp2 :
    FrameI wp1 wp1 |-- FrameI wp2 wp2 -* FrameI (@Mpar T U wp1 wp2) (Mpar wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    rewrite /Mpar/FrameI.
    iDestruct "D" as (??) "(D1 & D2 & K)".
    iExists _, _.
    iSplitL "D1 A".
    iApply "A". 2: eauto. iIntros (???) "X"; iApply "X".
    iSplitL "D2 B".
    iApply "B". 2: eauto. iIntros (???) "X"; iApply "X".
    iIntros (??????) "A B". iApply "C". iApply ("K" with "A B").
  Qed.


  (** lifting [Mpar] to homogeneous lists *)
  Fixpoint Mpars {T} (f : list (M T)) : M (list T) :=
    match f with
    | nil => mret nil
    | f :: fs => (fun '(v, vs) => v :: vs) <$> Mpar f (Mpars fs)
    end.

  Lemma Mpars_frame_strong {T} : forall (ls : list (M T)) Q Q',
      |-- (Forall x y pf, [| length x = length ls |] -* Q x y pf -* Q' x y pf) -*
          (Mpars ls Q) -* (Mpars ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "X"; iApply "X"; eauto.
    - iIntros "K".
      rewrite /M_map.
      rewrite /Mpar.
      iIntros "X".
      iDestruct "X" as (??) "(L & R & KK)".
      iExists _, _. iFrame "L".
      iDestruct (IHls with "[] R") as "IH".
      2: iFrame "IH".
      { instantiate (1:=fun x y pf => [| length x = length ls |] ** Q2 x y pf).
        iIntros (???) "$". eauto. }
      iIntros (??????) "? [% ?]".
      iApply ("K" $! (v1::v2) (FreeTemps.canon (f1 |*| f2))).
      { simpl. eauto. }
      iApply ("KK" $! v1 v2 f1 f2 pf1 pf2 with "[$] [$]").
  Qed.
  *)

  (** *** evaluation by a scheme *)

  (** [eval eo e1 e2] evaluates [e1], [e2] according to the evaluation scheme [eo] *)
  Definition eval2 (eo : evaluation_order.t) {T U} (e1 : Mlocal T) (e2 : Mlocal U) : Mlocal (T * U) :=
    match eo with
    | evaluation_order.nd => nd_seq e1 e2
    | evaluation_order.l_nd => Mseq e1 e2
    | evaluation_order.rl => (fun '(a,b) => (b,a)) <$> Mseq e2 e1
    end.

  (** [evals eo es] evaluates [es] according to the evaluation scheme [eo] *)
  Definition eval (eo : evaluation_order.t) {T} (es : list (Mlocal T)) : Mlocal (list T) :=
    match eo with
    | evaluation_order.nd => nd_seqs es
    | evaluation_order.l_nd =>
        match es with
        | e :: es => (fun '(a,b) => a :: b) <$> Mseq e (nd_seqs es)
        | [] => mret []
        end
    | evaluation_order.rl => (@rev _) <$> (seqs (rev es))
    end.

  Lemma eval_frame_strong {T} oe : forall (ls : list (Mlocal T)) Q Q',
      ([∗list] m ∈ ls, <affine> FrameI m m)%I
      |-- (Forall x y pf, on_normalI (fun x => [| length x = length ls |]) x -* Q x y pf -* Q' x y pf) -*
          eval oe ls Q -* eval oe ls Q'.
  Proof.
    destruct oe; intros.
    - rewrite /=/nd_seqs. iIntros "A B".
      iApply (nd_seqs'_frame_strong with "B"). done.
    - destruct ls; simpl.
      { iIntros "_ X"; iApply "X". done. }
      { iIntros "[X Y] K".
        rewrite /Mseq.
        iApply "X"; iIntros (???).
        case_match; try iApply "K"; eauto.
        iApply (nd_seqs'_frame_strong); eauto.
        iIntros (???) "P".
        iApply ("K" $! _ _ _).
        rewrite /on_normalI. destruct x0; simpl; eauto.
        iDestruct "P" as "%"; iPureIntro; eauto. }
    - simpl.
      iIntros "X K".
      iApply (seqs_frame_strong with "[X]").
      { iStopProof. induction ls; simpl; eauto.
        iIntros "[$ K]".
        iDestruct (IHls with "K") as "$". eauto. }
      { iIntros (???) "P". iApply ("K" $! _ _ _).
        destruct x; simpl; eauto.
        rewrite !length_rev. eauto. }
  Qed.

  (** TODO: integrate this *)
  #[global]
  Instance equiv_subseteq_subrelation {T} : @subrelation (M T) (≡) (⊆).
  Proof.
    red. intros. repeat intro.
    do 2 red in H. rewrite H. iApply _frame. 2: reflexivity.
    iIntros (???). iApply H0.
  Qed.

  #[global]
  Instance equiv_subseteq_proper {T} : Proper ((⊆) --> (⊆) ==> Basics.impl) (⊆@{M T}).
  Proof. repeat intro. red in H. Admitted.
  #[global]
  Instance equiv_subseteq_proper_equiv {T} : Proper ((≡) ==> (≡) ==> Basics.impl) (⊆@{M T}).
  Proof. repeat intro. red in H. Admitted.

  #[global]
  Instance equiv_RR {T} : RewriteRelation (≡@{M T}) := {}.
  #[global]
  Instance subseteq_RR {T} : RewriteRelation (⊆@{M T}) := {}.

  #[global] Instance WP_proper {T}
    : Proper ((≡) ==> eq ==> flip (⊢)) (WP (T:=T)).
  Proof.
    repeat intro; simpl; subst. rewrite /WP. red in H. red in H.
    rewrite H. reflexivity.
    simpl; intros. reflexivity.
  Qed.

  #[global]
  Instance Mbind_proper {T U}
    : Proper (pointwise_relation _ (⊆@{M U}) ==> (⊆@{M T}) ==> (⊆)) mbind.
  Proof.
    repeat intro.
    rewrite /M_bind/=. apply H0. intros. apply H. intros. apply H1.
  Qed.
  #[global]
  Instance Mbind_subseteq_proper {T U}
    : Proper (pointwise_relation _ (flip (⊆@{M U})) ==> flip (⊆@{M T}) ==> flip (⊆)) mbind.
  Proof.
    repeat intro.
    rewrite /M_bind/=. apply H0. intros. apply H. intros. apply H1.
  Qed.


  #[global] Instance WP_subseteq_proper {T}
    : Proper ((⊆) ==> eq ==> (⊢)) (WP (T:=T)).
  Proof.
    repeat intro. subst. rewrite /WP. apply H. eauto.
  Qed.
  #[global] Instance WP_subseteq_proper' {T}
    : Proper (flip (⊆) ==> eq ==> flip (⊢)) (WP (T:=T)).
  Proof.
    repeat intro. subst. rewrite /WP. apply H. eauto.
  Qed.

  Definition by_WP {T} (m1 m2 : M T) :
    (forall k, WP m1 k |-- WP m2 k) ->
    m1 ⊆ m2.
  Proof.
    rewrite /WP. repeat intro.
    rewrite H. iApply _frame. iIntros (???). iApply H0.
  Qed.

  #[global] Typeclasses Opaque WP M_bind M_ret M_map.

  #[local] Opaque FreeTemps.canon.
  Instance: forall {T} k K P, FromWand (WP (mbind k (Mproduce P)) K) P (WP (T:=T) (k ()) K).
  Proof.
    intros. red.
    rewrite /M_bind/WP/=.
    f_equiv.
    iApply _frame. iIntros (???).
    iApply K_entails.
    by rewrite FreeTemps.canon_equiv right_id.
  Qed.

  Instance: forall {T} K k P, IntoWand false false (WP (mbind k (Mproduce P)) K) P (WP (T:=T) (k ()) K).
  Proof.
    intros. red.
    rewrite /M_bind/WP/=.
    f_equiv.
    iApply _frame. iIntros (???).
    iApply K_entails.
    by rewrite FreeTemps.canon_equiv right_id.
  Qed.

  Lemma WP_Mbind_Mfupd {T} E1 E2 k K :
    WP (mbind k (Mfupd E1 E2)) K -|- |={E1,E2}=> WP (T:=T) (k ()) K.
  Proof.
    rewrite /WP/Mfupd/=. f_equiv.
    iSplit;
      by iApply _frame; iIntros (???); iApply K_entails; rewrite FreeTemps.canon_equiv right_id.
  Qed.
  Lemma WP_mret {T} (v : T) K :
    WP (mret v) K -|- K v FreeTemps.id _.
  Proof. rewrite /WP/M_ret/=. done. Qed.
  Lemma WP_Mbind_mret {T U} (v : T) (k : T -> M U) K :
    WP (mbind k (mret v)) K -|- WP (k v) K.
  Proof.
    rewrite /WP/M_bind/M_ret/=.
    iSplit;
      by iApply _frame; iIntros (???); iApply K_entails; rewrite FreeTemps.canon_equiv right_id.
  Qed.
  Lemma WP_Mbind_Mproduce {T} P k K :
    WP (mbind k (Mproduce P)) K -|- P -* WP (T:=T) (k ()) K.
  Proof.
    rewrite /WP/Mproduce/=. f_equiv.
    iSplit;
      by iApply _frame; iIntros (???); iApply K_entails; rewrite FreeTemps.canon_equiv right_id.
  Qed.

  (*
  Instance Mbind_params : Params (@bind) 4 := {}.
  Instance bi_entails_params : Params (@bi_entails) 1 := {}.
  *)

  Definition Kfree {T} (free : FreeTemps.t) (K : T -> forall free, FreeTemps.IsCanonical free -> mpred) : T -> forall free, FreeTemps.IsCanonical free -> mpred :=
    fun x f _ => K x (FreeTemps.canon (f >*> free)) _.
  Lemma WP_Mbind_frame {T U} (m : M T) (k1 k2 : T -> M U) K1 K2 :
    (Forall x free, WP (k1 x) (Kfree free K1) -* WP (k2 x) (Kfree free K2))
      |-- WP (mbind k1 m) K1 -* WP (mbind k2 m) K2.
  Proof.
    rewrite /WP/M_bind/=.
    iIntros "k"; iApply _frame; iIntros (???). iApply "k".
  Qed.
  Hint Opaque Kfree : typeclass_instances.
  Lemma WP_Mbind_Mbind {T U V} m1 (m2 : T -> M U) (m3 : U -> M V) K :
    WP (mbind m3 (mbind m2 m1)) K -|- WP (mbind (fun x => mbind m3 (m2 x)) m1) K.
  Proof.
    rewrite /M_bind/WP/=.
    iSplit;
      iApply _frame; iIntros (???); iApply _frame; iIntros (???); iApply _frame; iIntros (???);
      iApply K_entails; by rewrite !FreeTemps.canon_equiv assoc.
  Qed.

  Fixpoint tuple (ts : list Type) : Type :=
    match ts return Type with
    | nil => unit
    | t :: ts => t * tuple ts
    end.

  (* TODO: this is the heterogeneous extension of [eval] *)
  Parameter heval : forall (eo : evaluation_order.t) {ts} (x : tuple (M <$> ts)), M (tuple ts).
End with_cpp.

Notation "'letWP*' v := e 'in' k" := (mbind (fun v => k) e) (at level 0, v binder, k at level 200, only parsing).
