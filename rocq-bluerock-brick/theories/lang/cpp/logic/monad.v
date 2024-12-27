(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
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
Require Import bedrock.lang.bi.errors.

#[local] Set Primitive Projections.

(* expression continuations
 * - in full C++, this includes exceptions, but our current semantics
 *   doesn't treat those.
 *)
Definition epred `{cpp_logic} := mpred.
Notation epredO := mpredO (only parsing).
Bind Scope bi_scope with epred.

Declare Scope free_scope.
Delimit Scope free_scope with free.
Reserved Infix "|*|" (at level 30).
Reserved Infix ">*>" (at level 30).

Module FreeTemps.

  (* BEGIN FreeTemps.t *)
  Inductive t : Set :=
  | id (* = fun x => x *)
  | delete (ty : decltype) (p : ptr) (* = delete_val ty p *)
           (* ^^ this type has qualifiers but is otherwise a runtime type *)
  | delete_va (va : list (type * ptr)) (p : ptr)
  | seq (f g : t) (* = fun x => f $ g x *)
  | par (f g : t) (* = fun x => Exists Qf Qg, f Qf ** g Qg ** (Qf -* Qg -* x) *)
  .
  (* END FreeTemps.t *)

  Module Import notations.
    Bind Scope free_scope with t.
    Notation "1" := id : free_scope.
    Infix ">*>" := seq : free_scope.
    Infix "|*|" := par : free_scope.
  End notations.
  #[local] Open Scope free_scope.

  Inductive t_equiv : Equiv t :=
  | refl l : l ≡ l
  | sym l r : l ≡ r -> r ≡ l
  | trans a b c : a ≡ b -> b ≡ c -> a ≡ c

  | delete_ref ty p : delete (Tref ty) p ≡ delete (Trv_ref ty) p

  | seqA x y z : x >*> (y >*> z) ≡ (x >*> y) >*> z
  | seq_id_unitL l : 1 >*> l ≡ l
  | seq_id_unitR l : l >*> 1 ≡ l
  | seq_proper_ : ∀ {a b}, a ≡ b -> ∀ {c d}, c ≡ d -> a >*> c ≡ b >*> d

  | parC l r : l |*| r ≡ r |*| l
  | parA x y z : x |*| (y |*| z) ≡ (x |*| y) |*| z
  | par_id_unitL l : 1 |*| l ≡ l
  | par_proper_ : ∀ {a b}, a ≡ b -> ∀ {c d}, c ≡ d -> a |*| c ≡ b |*| d
  .
  Notation t_eq := (≡@{t}) (only parsing).

  #[global] Existing Instance t_equiv.
  #[global] Instance t_equivalence : Equivalence t_eq :=
    Build_Equivalence _ refl sym trans.

  #[global] Instance seq_assoc : Assoc equiv seq := seqA.
  #[global] Instance seq_left_id : LeftId equiv id seq := seq_id_unitL.
  #[global] Instance seq_right_id : RightId equiv id seq := seq_id_unitR.
  #[global] Instance seq_proper : Proper (t_eq ==> t_eq ==> t_eq) seq := @seq_proper_.

  #[global] Instance par_comm : Comm equiv par := parC.
  #[global] Instance par_left_id : LeftId equiv id par := par_id_unitL.
  #[global] Instance par_right_id : RightId equiv id par.
  Proof. intros x. by rewrite comm left_id. Qed.
  #[global] Instance par_proper : Proper (t_eq ==> t_eq ==> t_eq) par := @par_proper_.

  (**
  [pars ls] is the [FreeTemp] representing the destruction of each
  element in [ls] *in non-deterministic order*.
  *)
  Definition pars : list t -> t := foldr par 1.

  (**
  [seqs ls] is the [FreeTemp] representing the destruction of each
  element in [ls] sequentially from left-to-right, i.e. the first
  element in the list is run first.
  *)
  Definition seqs : list t -> t := foldr seq 1.

  (**
  [seqs_rev ls] is the [FreeTemp] representing the destruction of each
  element in [ls] sequentially from right-to-left, i.e. the first
  element in the list is destructed last.
  *)
  Definition seqs_rev : list t -> t := foldl (fun a b => seq b a) 1.
End FreeTemps.
Export FreeTemps.notations.
Notation FreeTemps := FreeTemps.t.
Notation FreeTemp := FreeTemps.t (only parsing).

(* continuations
 * C++ statements can terminate in 4 ways.
 *
 * note(gmm): technically, they can also raise exceptions; however,
 * our current semantics doesn't capture this. if we want to support
 * exceptions, we should be able to add another case,
 * `k_throw : val -> mpred`.
 *)
Variant ReturnType : Set :=
| Normal
| Break
| Continue
| ReturnVal (_ : ptr)
| ReturnVoid
.
#[global] Instance ReturnType_ihn : Inhabited ReturnType.
Proof. repeat constructor. Qed.

Canonical Structure rt_biIndex : biIndex :=
  {| bi_index_type := ReturnType
   ; bi_index_rel := eq
   |}.
Definition KpredI `{!cpp_logic thread_info Σ} : bi := monPredI rt_biIndex (@mpredI thread_info Σ).
#[global] Notation Kpred := (bi_car KpredI).

Definition KP `{cpp_logic} (P : ReturnType -> mpred) : Kpred := MonPred P _.
#[global] Arguments KP {_ _ _} _%_I : assert.
#[global] Hint Opaque KP : typeclass_instances.

Section KP.
  Context `{Σ : cpp_logic}.

  Lemma KP_frame (Q1 Q2 : ReturnType -> mpred) (rt : ReturnType) :
    Q1 rt -* Q2 rt
    |-- KP Q1 rt -* KP Q2 rt.
  Proof. done. Qed.
End KP.

Definition Kat_exit `{Σ : cpp_logic} (Q : mpred -> mpred) (k : Kpred) : Kpred :=
  KP $ fun rt => Q (k rt).
#[global] Hint Opaque Kat_exit : typeclass_instances.

Section Kat_exit.
  Context `{Σ : cpp_logic}.

  Lemma Kat_exit_frame (Q Q' : mpred -> mpred) (k k' : Kpred) :
    Forall R R' : mpred, (R -* R') -* Q R -* Q' R' |--
    Forall rt : ReturnType, (k rt -* k' rt) -*
    Kat_exit Q k rt -* Kat_exit Q' k' rt.
  Proof.
    iIntros "HQ %rt Hk". destruct rt; cbn.
    all: by iApply "HQ".
  Qed.
End Kat_exit.

(*
NOTE KpredI does not embed into mpredI because it doesn't respect
existentials.
*)
#[global] Instance mpred_Kpred_BiEmbed `{Σ : cpp_logic} : BiEmbed mpredI KpredI := _.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* the monad for expression evaluation *)
  #[program]
  Definition M_index (t : Type) : biIndex :=
    {| bi_index_type := t -> FreeTemps.t -> mpred
     ; bi_index_inhabited := _ |}.
  Definition M (t : Type) := monPredI (M_index t) mpred.

  (*
  Definition Mfree_all {t : Set} (m : M t) : M t :=
    MonPred (I:=M_index t) (fun K => m (fun v free => interp free $ K v FreeTemps.id)) _.
   *)

  Definition Massume (P : Prop) : M unit :=
    MonPred (I:=M_index unit) (fun K => [| P |] -* K () FreeTemps.id) _.
  Definition Mrequire (P : Prop) : M unit :=
    MonPred (I:=M_index unit) (fun K => [| P |] ** K () FreeTemps.id) _.

  Definition Mret {t : Type} (v : t) : M t :=
    MonPred (I:=M_index t) (fun K => K v FreeTemps.id) _.

  Definition Mmap {t u : Type} (f : t -> u) (m : M t) : M u :=
    MonPred (I:=M_index u) (fun K => m (fun t => K (f t))) _.

  Definition Mnd (t : Type) : M t :=
    MonPred (I:=M_index t) (fun K => ∀ x : t, K x FreeTemps.id)%I _.
  Definition Mangelic (t : Type) : M t :=
    MonPred (I:=M_index t) (fun K => ∃ x : t, K x FreeTemps.id)%I _.

  Definition Mproduce (m : mpred) : M unit :=
    MonPred (I:=M_index unit) (fun K => m -* K () FreeTemps.id) _.
  Definition Mconsume (m : mpred) : M unit :=
    MonPred (I:=M_index unit) (fun K => m ** K () FreeTemps.id) _.

  Definition Mub {t : Type} : M t :=
    MonPred (I:=M_index t) (fun _ => False)%I _.
  Definition Many {t : Type} : M t :=
    MonPred (I:=M_index t) (fun _ => True)%I _.

  Definition Merror {t : Type} {ERR : Type} (err : ERR) : M t :=
    MonPred (I:=M_index t) (fun _ => ERROR err) _.

  Definition Mboth {t} (a b : M t) : M t :=
    MonPred (I:=M_index t) (fun K => a K //\\ b K) _.

  Definition Mread {t} (R : t -> mpred) : M t :=
    MonPred (I:=M_index t) (fun K => Exists v, R v ** (R v -* K v FreeTemps.id)) _.
  Definition Mread_with {TT : tele} (R : TT -t> mpred) : M TT :=
    MonPred (I:=M_index TT) (fun K => ∃.. v, tele_app R v ** (tele_app R v -* K v FreeTemps.id))%I _.

  Definition Mpush_free (f : FreeTemps.t) : M () :=
    MonPred (I:=M_index ()) (fun K => K () f) _.

  (** The [Proper]ness relation that should typically be used for [M]. *)
  Definition Mrel T : M T -> M T -> Prop :=
    (pointwise_relation _ (pointwise_relation _ (⊢)) ==> (⊢))%signature.
  (** This relation is _weaker_ because it requires the argument to respect [FreeTemps.t_eq]. *)
  Definition Mequiv T : M T -> M T -> Prop :=
    (pointwise_relation _ (FreeTemps.t_eq ==> (⊣⊢)) ==> (⊣⊢))%signature.

  Definition Mframe {T} (a b : M T) : mpred :=
    Forall Q Q', (Forall x y, Q x y -* Q' x y) -* a Q -* b Q'.

  Definition WP {T} (m : M T) (Q : T -> FreeTemps.t -> mpred) : mpred :=
    m Q.

  Definition Mimpl {T} (a b : M T) : mpred :=
    ∀ Q, a Q -* b Q.

  Lemma WP_impl {T} (a b : M T) Q : Mimpl a b |-- WP a Q -* WP b Q.
  Proof. rewrite /Mimpl. iIntros "X". iApply "X". Qed.

  Lemma Mmap_frame_strong {T U} c (f : T -> U) :
    Mframe c c
    |-- Forall Q Q', (Forall x y, Q (f x) y -* Q' (f x) y) -* Mmap f c Q -* Mmap f c Q'.
  Proof.
    rewrite /Mframe/Mmap; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.

  Lemma Mmap_frame {T U} c (f : T -> U) :
    Mframe c c |-- Mframe (Mmap f c) (Mmap f c).
  Proof.
    rewrite /Mframe/Mmap; iIntros "A" (??) "B".
    iApply "A". iIntros (??); iApply "B".
  Qed.

  #[local] Definition Mbind {T U} (c : M T) (k : T -> M U) : M U :=
    MonPred (I:=M_index U) (fun K => c (fun v f => k v (fun v' f' => K v' (f' >*> f)%free))) _.

  Lemma Mbind_frame {T U} c (k : T -> M U) :
    Mframe c c |-- (Forall x, Mframe (k x) (k x)) -* Mframe (Mbind c k) (Mbind c k).
  Proof.
    rewrite /Mframe/Mbind; iIntros "A B" (??) "C".
    iApply "A". iIntros (??). iApply "B".
    iIntros (??); iApply "C".
  Qed.

  (** *** Indeterminately sequenced computations
      Note that [FreeTemps.t] is sequenced in reverse order of construction
      to encode the stack discipline guaranteed by C++.
      (CITATION NEEDED)
   *)
  Definition nd_seq {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    MonPred (I:=M_index (T * U))
      (fun K => wp1 (fun v1 f1 => wp2 (fun v2 f2 => K (v1,v2) (f2 >*> f1)%free))
        //\\ wp2 (fun v2 f2 => wp1 (fun v1 f1 => K (v1,v2) (f1 >*> f2)%free))) _.

  Lemma nd_seq_frame {T U} wp1 wp2 :
    Mframe wp1 wp1 |-- Mframe wp2 wp2 -* Mframe (@nd_seq T U wp1 wp2) (nd_seq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    iSplit; [ iDestruct "D" as "[D _]" | iDestruct "D" as "[_ D]" ]; iRevert "D".
    { iApply "A". iIntros (??). iApply "B"; iIntros (??). iApply "C". }
    { iApply "B". iIntros (??). iApply "A"; iIntros (??). iApply "C". }
  Qed.

  (* Lifting non-deterministic sequencing to lists.

     NOTE: this is like the semantics of argument evaluation in C++.
   *)
  (*
  Fixpoint nd_seqs' {T} (f : nat) (qs : list (M T)) {struct f} : M (list T) :=
    match qs with
    | nil => Mret nil
    | _ :: _ =>
      match f with
      | 0 => Mub
      | S f => fun Q =>
        Forall pre post q, [| qs = pre ++ q :: post |] -*
               let lpre := length pre in
               Mbind q (fun t => Mmap (fun ts => firstn lpre ts ++ t :: skipn lpre ts) (nd_seqs' f (pre ++ post))) Q
      end
    end.
   *)

  Definition nd_seqs {T} (qs : list (M T)) : M (list T). (* := @nd_seqs' T (length qs) qs. *) Admitted.

  (*
  Lemma nd_seqs'_frame_strong {T} n : forall (ls : list (M T)) Q Q',
      n = length ls ->
      Forall x y, [| length x = length ls |] -* Q x y -* Q' x y
      |-- ([∗list] m ∈ ls, Mframe m m) -*
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
      ([∗list] m ∈ ls, Mframe m m)
      |-- Mframe (nd_seqs' n ls) (nd_seqs' n ls).
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
  Lemma nd_seqs_frame : forall {T} (ms : list (_ T)),
      ([∗list] m ∈ ms, Mframe m m) |-- Mframe (nd_seqs ms) (nd_seqs ms).
  Proof. intros. by iApply nd_seqs'_frame. Qed.

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
  Definition Mseq {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    Mbind wp1 (fun v => Mmap (fun x => (v, x)) wp2).

  Lemma Mseq_frame {T U} wp1 wp2 :
    Mframe wp1 wp1 |-- Mframe wp2 wp2 -* Mframe (@Mseq T U wp1 wp2) (Mseq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C".
    rewrite /Mseq.
    iApply (Mbind_frame with "A [B]"); last iAssumption.
    iIntros (???) "X". iApply (Mmap_frame with "B"). done.
  Qed.

  (** [seqs es] is sequential evaluation of [es] *)
  Fixpoint seqs {T} (es : list (M T)) : M (list T) :=
    match es with
    | nil => Mret []
    | e :: es => Mmap (fun '(a,b) => a:: b) (Mseq e (seqs es))
    end.

  Lemma seqs_frame_strong {T} : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, Mframe m m)%I
      |-- (Forall x y, [| length x = length ls |] -* Q x y -* Q' x y) -*
          (seqs ls Q) -* (seqs ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "_ X"; iApply "X"; eauto.
    - iIntros "[A AS] K".
      rewrite /Mbind. iApply "A".
      iIntros (??).
      iApply (IHls with "AS").
      iIntros (???).
      iApply "K". simpl. eauto.
  Qed.

  (** *** interleaving of monadic values

      We encode interleaving through concurrency which we represent through
      separable resources.

      NOTE: this is like the semantics of argument evaluation in C
   *)
  Definition Mpar {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    MonPred (I:=M_index (T * U))
      (fun Q => Exists Q1 Q2, wp1 Q1 ** wp2 Q2 ** (Forall v1 v2 f1 f2, Q1 v1 f1 -* Q2 v2 f2 -* Q (v1,v2) (f1 |*| f2)%free)) _.

  Lemma Mpar_frame {T U} wp1 wp2 :
    Mframe wp1 wp1 |-- Mframe wp2 wp2 -* Mframe (@Mpar T U wp1 wp2) (Mpar wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    rewrite /Mpar/Mframe.
    iDestruct "D" as (??) "(D1 & D2 & K)".
    iExists _, _.
    iSplitL "D1 A".
    iApply "A". 2: eauto. iIntros (??) "X"; iApply "X".
    iSplitL "D2 B".
    iApply "B". 2: eauto. iIntros (??) "X"; iApply "X".
    iIntros (????) "A B". iApply "C". iApply ("K" with "A B").
  Qed.


  (** lifting [Mpar] to homogeneous lists *)
  Fixpoint Mpars {T} (f : list (M T)) : M (list T) :=
    match f with
    | nil => Mret nil
    | f :: fs => Mmap (fun '(v, vs) => v :: vs) $ Mpar f (Mpars fs)
    end.

  Lemma Mpars_frame_strong {T} : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, Mframe m m)%I
      |-- (Forall x y, [| length x = length ls |] -* Q x y -* Q' x y) -*
          (Mpars ls Q) -* (Mpars ls Q').
  Proof.
    induction ls; simpl; intros.
    - iIntros "_ X"; iApply "X"; eauto.
    - iIntros "[A AS] K".
      rewrite /Mmap.
      rewrite /Mpar.
      iIntros "X".
      iDestruct "X" as (??) "(L & R & KK)".
      iExists _, _. iFrame "L".
      iDestruct (IHls with "AS [] R") as "IH".
      2: iFrame "IH".
      { instantiate (1:=fun x y => [| length x = length ls |] ** Q2 x y).
        iIntros (???) "$". eauto. }
      iIntros (????) "? [% ?]".
      iApply "K".
      { simpl. eauto. }
      iApply ("KK" with "[$] [$]").
  Qed.

  (** *** evaluation by a scheme *)

  (** [eval eo e1 e2] evaluates [e1], [e2] according to the evaluation scheme [eo] *)
  Definition eval2 (eo : evaluation_order.t) {T U} (e1 : M T) (e2 : M U) : M (T * U) :=
    match eo with
    | evaluation_order.nd => nd_seq e1 e2
    | evaluation_order.l_nd => Mseq e1 e2
    | evaluation_order.rl => Mmap (fun '(a,b) => (b,a)) $ Mseq e2 e1
    end.

  (** [evals eo es] evaluates [es] according to the evaluation scheme [eo] *)
  Definition eval (eo : evaluation_order.t) {T} (es : list (M T)) : M (list T) :=
    match eo with
    | evaluation_order.nd => nd_seqs es
    | evaluation_order.l_nd =>
        match es with
        | e :: es => Mbind e (fun v => Mmap (fun vs => v :: vs) (nd_seqs es))
        | [] => Mret []
        end
    | evaluation_order.rl => Mmap (@rev _) (seqs (rev es))
    end.

  Lemma eval_frame_strong {T} oe : forall (ls : list (M T)) Q Q',
      ([∗list] m ∈ ls, Mframe m m)%I
      |-- (Forall x y, [| length x = length ls |] -* Q x y -* Q' x y) -*
          eval oe ls Q -* eval oe ls Q'.
  Proof. (*
    destruct oe; intros.
    - rewrite /=/nd_seqs. iIntros "A B".
      iApply (nd_seqs'_frame_strong with "B A"). done.
    - simpl.
      destruct ls; simpl.
      { iIntros "_ X"; iApply "X". done. }
      { iIntros "[X Y] K".
        iApply "X". iIntros (??).
        iApply (nd_seqs'_frame_strong with "[K] Y"); eauto.
        iIntros (???).
        rewrite /Mret.
        iApply "K". simpl; eauto. }
    - simpl.
      iIntros "X K".
      rewrite /Mmap. iApply (seqs_frame_strong with "[X]").
      { iStopProof. induction ls; simpl; eauto.
        iIntros "[$ K]".
        iDestruct (IHls with "K") as "$". eauto. }
      { iIntros (???); iApply "K".
        rewrite length_rev. eauto. rewrite -(length_rev ls). eauto. }
  Qed. *) Admitted.

  Fixpoint tuple (ts : list Type) : Type :=
    match ts return Type with
    | nil => unit
    | t :: ts => t * tuple ts
    end.

  (* TODO: this is the heterogeneous extension of [eval] *)
  Parameter heval : forall (eo : evaluation_order.t) {ts} (x : tuple ((fun x => bi_car (M x)) <$> ts)), M (tuple ts).
End with_cpp.

Notation "'letWP*' v := e 'in' k" := (Mbind e (fun v => k)) (at level 0, v binder, k at level 200).
