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
Require Import bedrock.lang.bi.linearity.
#[local] Set Primitive Projections.

Import linearity.

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

  #[global] Instance t_inh : Inhabited t.
  Proof. repeat constructor. Qed.

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
Variant ReturnType {t : Type} : Type :=
| Normal (result : t)
| Break
| Continue
| ReturnVal (_ : ptr)
| ReturnVoid
.
Arguments ReturnType _ : clear implicits.

#[global] Instance ReturnType_inh {T} : Inhabited (ReturnType T).
Proof. constructor. exact ReturnVoid. Qed.

Canonical Structure rt_biIndex t : biIndex :=
  {| bi_index_type := ReturnType t * FreeTemps.t
   ; bi_index_rel := eq
   |}.
Definition KpredI `{!cpp_logic thread_info Σ} t : bi := monPredI (rt_biIndex t) (@mpredI thread_info Σ).
#[global] Notation Kpred t := (bi_car (KpredI t)).

Definition KP `{cpp_logic} {T} (P : ReturnType T -> FreeTemps.t -> mpred) : Kpred T := MonPred (fun '(rt, free) => P rt free) _.
#[global] Arguments KP {_ _ _ _} _%_I : assert.
#[global] Hint Opaque KP : typeclass_instances.

Section KP.
  Context `{Σ : cpp_logic}.

  Lemma KP_frame {T} (Q1 Q2 : ReturnType T -> FreeTemps.t -> mpred) (rt : ReturnType T) free :
    Q1 rt free -* Q2 rt free
    |-- KP Q1 (rt, free) -* KP Q2 (rt, free).
  Proof. done. Qed.
End KP.

(*
(** *** [Kreturn Q] -- [Q] is applied to the returned value *)
Definition Kreturn_inner `{Σ : cpp_logic, σ : genv} (Q : ptr -> mpred) (rt : ReturnType ()) : mpred :=
  match rt with
  | Normal _ => Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p
  | ReturnVoid => Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p
  | ReturnVal p => Q p
  | _ => False
  end.
#[global] Arguments Kreturn_inner _ _ _ _ _ !rt /.

Definition Kreturn `{Σ : cpp_logic, σ : genv} (Q : ptr -> mpred) : Kpred () :=
  KP $ Kreturn_inner Q.
#[global] Hint Opaque Kreturn : typeclass_instances.

Section Kreturn.
  Context `{Σ : cpp_logic, σ : genv}.

  Lemma Kreturn_frame (Q Q' : ptr -> mpred) (rt : ReturnType ()) :
    Forall p, Q p -* Q' p
    |-- Kreturn Q rt -* Kreturn Q' rt.
  Proof.
    iIntros "HQ". destruct rt; cbn; auto.
    all: iIntros "HR" (?) "R"; iApply "HQ"; by iApply "HR".
  Qed.
End Kreturn.
*)

(* Run [Q] when the evaluation completes *)
Definition Kat_exit `{Σ : cpp_logic} {T} (Q : mpred -> mpred) (k : Kpred T) : Kpred T :=
  KP $ fun rt free => Q (k (rt, free)).
#[global] Hint Opaque Kat_exit : typeclass_instances.

Section Kat_exit.
  Context `{Σ : cpp_logic}.

  Lemma Kat_exit_frame {T} (Q Q' : mpred -> mpred) (k k' : Kpred T) :
    Forall R R' : mpred, (R -* R') -* Q R -* Q' R' |--
                           Forall rt, (k rt -* k' rt) -*
                                        Kat_exit Q k rt -* Kat_exit Q' k' rt.
  Proof.
    iIntros "HQ %rt Hk". destruct rt; cbn.
    all: by iApply "HQ".
  Qed.
End Kat_exit.

(** The type of the interpreter for [FreeTemps.t].
    We treat throwing exceptions from destructors as UB since this is at least strongly frowned upon.
 *)
Definition Mfree `{Σ : cpp_logic} := FreeTemps.t -> mpred -> mpred.

(** Clean up the temporaries early on exceptional control flow, otherwise, extend *)
Definition Ktemps `{Σ : cpp_logic} {T} (free : FreeTemps.t) (k : Kpred T) : Kpred T :=
  KP $ fun rt free' =>
      let mk x := k (x, free' >*> free)%free in
      match rt with
      | Normal v => mk $ Normal v
      | Continue => mk Continue
      | Break => mk Break
      | ReturnVal p => mk (ReturnVal p)
      | ReturnVoid => mk ReturnVoid
      end.

(** Clean up all the temporaries before running [k] *)
Definition Kfree `{Σ : cpp_logic} (interp : Mfree) {T} (k : Kpred T) : Kpred T :=
  KP $ fun rt free => interp free $ k (rt, FreeTemps.id).

(** *** [Kbind Q k] *)
Definition Kbind_inner `{Σ : cpp_logic} {T U} (Q : T -> Kpred U -> mpred) (k : Kpred U) (rt : ReturnType T) (free : FreeTemps.t) : mpred :=
  match rt with
  | Normal v => Q v (Ktemps free k)
  | Break => k (Break, free)
  | Continue => k (Continue, free)
  | ReturnVal p => k (ReturnVal p, free)
  | ReturnVoid => k (ReturnVoid, free)
  end.

Definition Kbind `{Σ : cpp_logic} {T U} (Q : T -> Kpred U -> mpred) (k : Kpred U) : Kpred T :=
  KP $ Kbind_inner Q k.

Section Kbind.
  Context `{Σ : cpp_logic}.

  Lemma Kbind_frame {T U} (Q1 Q2 : T -> Kpred U -> mpred) (k1 k2 : Kpred U) rt :
    <affine> (Forall (k1 k2 : Kpred U) x, (Forall rt, k1 rt -* k2 rt) -* Q1 x k1 -* Q2 x k2)
    |-- (Forall rt, k1 rt -* k2 rt) -*
        Kbind Q1 k1 rt -* Kbind Q2 k2 rt.
  Proof.
    iIntros "HQ Hk". destruct rt; cbn; try iExact "Hk".
    rewrite /Kbind_inner. case_match; eauto.
    rewrite /Ktemps.
    rewrite bi.affinely_elim.
    iApply ("HQ" with "[Hk]").
    iIntros (?). rewrite /KP/=.
    case_match; subst. case_match; eauto.
  Qed.
End Kbind.

(* A simple version of [Kbind] *)
Notation Kpure Q := (Kbind (fun a k => Q a (fun a' => k (Normal a', FreeTemps.id)))).

(** *** [Kseq Q k] *)
Definition Kseq `{Σ : cpp_logic} (Q : Kpred () -> mpred) (k : Kpred ()) : Kpred () :=
  Kbind (fun _ => Q) k.
#[global] Hint Opaque Kseq : typeclass_instances.

Section Kseq.
  Context `{Σ : cpp_logic}.

  Lemma Kseq_frame (Q1 Q2 : Kpred () -> mpred) (k1 k2 : Kpred ()) rt :
    <affine> (Forall k1 k2 : Kpred _, (Forall rt, k1 rt -* k2 rt) -* Q1 k1 -* Q2 k2)
    |-- (Forall rt, k1 rt -* k2 rt) -*
        Kseq Q1 k1 rt -* Kseq Q2 k2 rt.
  Proof.
    rewrite /Kseq. iIntros "X"; iApply Kbind_frame.
    iModIntro. rewrite bi.affinely_elim.
    iIntros (???) "K". iApply "X". eauto.
  Qed.
End Kseq.

(* TODO: move to stmt
(* loop with invariant `I` *)
Definition Kloop_inner `{Σ : cpp_logic} (I : mpred) (Q : Kpred ()) (rt : ReturnType ()) (free : FreeTemps.t) : mpred :=
  match rt with
  | Break | Normal _ => Q (Normal (), free)
  | Continue => wp_interp free $ I
  | ReturnVal _ | ReturnVoid => Q (rt, free)
  end.
#[global] Arguments Kloop_inner _ _ _ _ _ !rt /.

Definition Kloop `{Σ : cpp_logic} (I : mpred) (Q : Kpred ()) : Kpred () :=
  KP $ Kloop_inner I Q.
#[global] Hint Opaque Kloop : typeclass_instances.

Section Kloop.
  Context `{Σ : cpp_logic}.

  Lemma Kloop_frame (I1 I2 : mpred) (k1 k2 : Kpred ()) (rt : ReturnType ()) :
    <affine> (I1 -* I2) |--
    <affine> (Forall rt, k1 rt -* k2 rt) -*
    Kloop I1 k1 rt -* Kloop I2 k2 rt.
  Proof.
    iIntros "HI Hk". destruct rt; cbn.
    all: first [ iExact "Hk" | iApply "HI" ].
  Qed.
End Kloop.
*)


(*
NOTE KpredI does not embed into mpredI because it doesn't respect
existentials.
#[global] Instance mpred_Kpred_BiEmbed `{Σ : cpp_logic} : BiEmbed mpredI KpredI := _.
*)

(** * Regions
    To model the stack frame in separation logic, we use a notion of regions
    that are threaded through the semantics.

    We instantiate [region] as a finite map from variables to their addresses
    (implemented as an association list).
*)
Inductive region : Set :=
| Remp (this var_arg : option ptr) (ret_type : decltype)
| Rbind (_ : localname) (_ : ptr) (_ : region).

Fixpoint get_location (ρ : region) (b : localname) : option ptr :=
  match ρ with
  | Remp _ _ _ => None
  | Rbind x p rs =>
    if decide (b = x) then Some p
    else get_location rs b
  end.

Fixpoint get_this (ρ : region) : option ptr :=
  match ρ with
  | Remp this _ _ => this
  | Rbind _ _ rs => get_this rs
  end.

Fixpoint get_return_type (ρ : region) : decltype :=
  match ρ with
  | Remp _ _ ty => ty
  | Rbind _ _ rs => get_return_type rs
  end.

Fixpoint get_va (ρ : region) : option ptr :=
  match ρ with
  | Remp _ va _ => va
  | Rbind _ _ rs => get_va rs
  end.

(** [_local ρ b] returns the [ptr] that stores the local variable [b].
 *)
Definition _local (ρ : region) (b : ident) : ptr :=
  match get_location ρ b with
  | Some p => p
  | _ => invalid_ptr
  end.
Arguments _local !_ !_ / : simpl nomatch, assert.

(** [_this ρ] returns the [ptr] that [this] is bound to.

    NOTE because [this] is [const], we actually store the value directly
    rather than indirectly representing it in memory.
 *)
Definition _this (ρ : region) : ptr :=
  match get_this ρ with
  | Some p => p
  | _ => invalid_ptr
  end.
Arguments _this !_ / : assert.

(** ** The C++ Evaluation Monad *)
Module cpp_m.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  (* the monad for expression evaluation *)
  Definition M (T : Type) : Type :=
    Kpred T -> mpred.

  (** The [Proper]ness relation that should typically be used for [M]. *)
  Definition Mrel T : M T -> M T -> Prop :=
    ((⊢) ==> (⊢))%signature.
  (** This relation is _weaker_ because it requires the argument to respect [FreeTemps.t_eq]. *)
  Definition Mequiv T : M T -> M T -> Prop :=
    ((⊣⊢) ==> (⊣⊢))%signature.

  Definition Mframe {T} (a b : M T) : mpred :=
    Forall Q Q' : Kpred T, (Forall v, Q v -* Q' v) -* a Q -* b Q'.

  Definition Mret {T} (t : T) : M T :=
    fun K => K (Normal t, FreeTemps.id).

  #[local] Instance ResultVal_fmap : FMap ReturnType :=
    fun _ _ f x => match x with
                | Normal x => Normal $ f x
                | Break => Break
                | Continue => Continue
                | ReturnVoid => ReturnVoid
                | ReturnVal v => ReturnVal v
                end.
  #[local] Instance index_fmap : FMap (fun t => rt_biIndex t) :=
    fun _ _ f '(x, free) => (f <$> x, free).

  Definition Mmap {T U} (f : T -> U) (t : M T) : M U :=
    fun K : Kpred U => t $ MonPred (fun rt_free => K ((f <$> rt_free.1), rt_free.2)) _.

  Lemma Mmap_frame_strong {T U} c (f : T -> U) :
    Mframe c c
    |-- Forall Q Q' : Kpred U, (Forall x, Q (index_fmap _ _ f x) -* Q' (index_fmap _ _ f x)) -* Mmap f c Q -* Mmap f c Q'.
  Proof.
    rewrite /Mframe/Mmap; iIntros "A" (??) "B".
    iApply "A". iIntros (?). simpl. iApply ("B" $! (v.1, v.2)).
  Qed.

  Lemma Mmap_frame {T U} c (f : T -> U) :
    Mframe c c |-- Mframe (Mmap f c) (Mmap f c).
  Proof.
    rewrite /Mframe/Mmap; iIntros "A" (??) "B".
    iApply "A". iIntros (?); iApply "B".
  Qed.

  #[local] Definition Mbind {T U} (c : M T) (k : T -> M U) : M U :=
    fun K => c (Kbind k K).

  Lemma Mbind_frame {T U} c (k : T -> M U) :
    Mframe c c |-- <affine> (Forall x, Mframe (k x) (k x)) -* Mframe (Mbind c k) (Mbind c k).
  Proof.
    rewrite /Mframe/Mbind; iIntros "A B" (??) "C".
    iApply "A". iIntros ([??]). iApply (Kbind_frame with "[B]"); eauto.
    iModIntro. rewrite bi.affinely_elim.
    by iIntros (???) "C"; iApply "B".
  Qed.

  (** *** Indeterminately sequenced computations
      Note that [FreeTemps.t] is sequenced in reverse order of construction
      to encode the stack discipline guaranteed by C++.
      (CITATION NEEDED)
   *)
  Definition nd_seq {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    fun K => Mbind wp1 (fun v1 => Mbind wp2 (fun v2 => Mret (v1, v2))) K
     //\\ Mbind wp2 (fun v2 => Mbind wp1 (fun v1 => Mret (v1, v2))) K.

  Lemma nd_seq_frame {T U} wp1 wp2 :
    <affine> Mframe wp1 wp1 |-- <affine> Mframe wp2 wp2 -* Mframe (@nd_seq T U wp1 wp2) (nd_seq wp1 wp2).
  Proof.
    iIntros "A B" (??) "C D".
    iSplit; [ iDestruct "D" as "[D _]" | iDestruct "D" as "[_ D]" ]; iRevert "D".
    { rewrite bi.affinely_elim. iApply "A". iIntros (?).
      iApply (Kbind_frame with "[B] [C]"); eauto.
      iModIntro; rewrite bi.affinely_elim.
      iIntros (???) "A".
      iApply "B".
      iIntros (?).
      iApply Kbind_frame; eauto.
      iModIntro.
      iIntros (???) "X"; iApply "X". }
    { rewrite (bi.affinely_elim (Mframe wp2 wp2)). iApply "B". iIntros (?).
      iApply (Kbind_frame with "[A] [C]"); eauto.
      iModIntro; rewrite bi.affinely_elim.
      iIntros (???) "B".
      iApply "A".
      iIntros (?).
      iApply Kbind_frame; eauto.
      iModIntro.
      iIntros (???) "X"; iApply "X". }
  Qed.

  (* Lifting non-deterministic sequencing to lists.

     NOTE: this is like the semantics of argument evaluation in C++.
   *)
  Fixpoint nd_seqs' {T} (f : nat) (qs : list (M T)) {struct f} : M (list T) :=
    match qs with
    | nil => Mret nil
    | _ :: _ =>
      match f with
      | 0 => funI _ => False
      | S f => fun Q =>
        Forall pre post q, [| qs = pre ++ q :: post |] -*
               let lpre := length pre in
               Mbind q (fun t => Mmap (fun ts => firstn lpre ts ++ t :: skipn lpre ts) (nd_seqs' f (pre ++ post))) Q
      end
    end.

  Definition nd_seqs {T} qs := @nd_seqs' T (length qs) qs.

  Lemma nd_seqs'_frame_strong {T} n : forall (ls : list (M T)) (K K' : Kpred (list T)),
      n = length ls ->
      Forall (x : ReturnType (list T) * FreeTemps.t), [| match x.1 with
                                                         | Normal v => length v = length ls
                                                         | _ => True
                                                         end |] -* K x -* K' x
      |-- <affine> ([∗list] m ∈ ls, Mframe m m) -*
          nd_seqs' n ls K -* nd_seqs' n ls K'.
  Proof.
    induction n; simpl; intros.
    { case_match; eauto.
      subst. simpl.
      iIntros "X _". iApply "X". eauto. }
    { destruct ls; first by exfalso; simpl in *; congruence.
      inversion H.
      iIntros "X LS Y" (???) "%P".
      iSpecialize ("Y" $! pre).
      iSpecialize ("Y" $! post).
      iSpecialize ("Y" $! q).
      iDestruct ("Y" with "[]") as "Y"; first eauto.
      rewrite P.
      iDestruct "LS" as "(a&b&c)".
      iRevert "Y". rewrite /Mbind.
      rewrite (bi.affinely_elim (Mframe q q)).
      iApply "b".
      iIntros (?).
      rewrite /Mmap.
      subst.
      assert (length ls = length (pre ++ post)).
      { have: (length (m :: ls) = length (pre ++ q :: post)) by rewrite P.
        rewrite !length_app /=. lia. }
      rewrite /Kbind/Kbind_inner/KP/=.
      case_match; case_match;
        try solve [ iApply "X"; simpl; eauto ].
      iDestruct (IHn with "[X]") as "X". eassumption.
      2:{
        iDestruct ("X" with "[a c]") as "X".
        iSplitL "a"; eauto.
        iApply "X". }
      simpl. iIntros (?) "%" => /=.
      destruct x as [[] ?]; simpl in *; iApply "X"; eauto.
      iPureIntro => /=. revert H0 H3; simpl; rewrite !length_app/=; intros.
      rewrite firstn_length_le; [ | lia ].
      rewrite length_skipn; lia. }
  Qed.

  Lemma nd_seqs'_frame {T} n : forall (ls : list (M T)),
      n = length ls ->
      <affine> ([∗list] m ∈ ls, Mframe m m)
      |-- Mframe (nd_seqs' n ls) (nd_seqs' n ls).
  Proof.
    intros.
    iIntros "X" (??) "Y".
    iApply (nd_seqs'_frame_strong with "[Y] X"); eauto.
    iIntros (??); iApply "Y".
  Qed.
  Lemma nd_seqs_frame : forall {T} (ms : list (_ T)),
      <affine> ([∗list] m ∈ ms, Mframe m m) |-- Mframe (nd_seqs ms) (nd_seqs ms).
  Proof. intros. by iApply nd_seqs'_frame. Qed.

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
  Definition Mseq {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    Mbind wp1 (fun v => Mmap (fun x => (v, x)) wp2).

  Lemma Mseq_frame {T U} wp1 wp2 :
    <affine> Mframe wp1 wp1 |-- <affine> Mframe wp2 wp2 -* Mframe (@Mseq T U wp1 wp2) (Mseq wp1 wp2).
  Proof.
    iIntros "A B" (??) "c".
    rewrite /Mseq.
    iApply (Mbind_frame with "A [B]"); last iAssumption.
    iModIntro; rewrite bi.affinely_elim.
    iIntros (?). iApply (Mmap_frame with "B").
  Qed.

  (** [seqs es] is sequential evaluation of [es] *)
  Fixpoint seqs {T} (es : list (M T)) : M (list T) :=
    match es with
    | nil => Mret []
    | e :: es => Mmap (fun '(a,b) => a:: b) (Mseq e (seqs es))
    end.

  Lemma seqs_frame_strong {T} : forall (ls : list (M T)) (Q Q' : Kpred (list T)),
      <affine> ([∗list] m ∈ ls, Mframe m m)%I
      |-- (Forall x, [| match x.1 with
                        | Normal x => length x = length ls
                        | _ => True
                        end |] -* Q x -* Q' x) -*
          seqs ls Q -* seqs ls Q'.
  Proof.
    induction ls; simpl; intros.
    - iIntros "_ X"; iApply "X"; eauto.
    - iIntros "[A AS] K".
      rewrite /Mbind.
      rewrite (bi.affinely_elim (Mframe a a)).
      iApply "A".
      iIntros (?).
      rewrite /Kbind/Kbind_inner/=.
      case_match; case_match; try iApply "K"; eauto.
      iApply (IHls with "AS").
      iIntros (??).
      destruct x as [[] ?] => /=; try iApply "K"; simpl; eauto.
  Qed.

  (*
  (** *** interleaving of monadic values

      We encode interleaving through concurrency which we represent through
      separable resources. However, this does not work when the different
      values can return in different ways. Capturing this requires a
      finer-grained interleaving that this monad currently does not support.

      NOTE: this is like the semantics of argument evaluation in C.
   *)
  Definition Mpar {T U} (wp1 : M T) (wp2 : M U) : M (T * U) :=
    fun Q => Exists Q1 Q2, wp1 Q1 ** wp2 Q2 ** (Forall v1 v2 f1 f2, Q1 v1 f1 -* Q2 v2 f2 -* Q (v1,v2) (f1 |*| f2)%free).

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
  *)

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

  Lemma eval_frame_strong {T} oe : forall (ls : list (M T)) (Q Q' : Kpred (list T)),
      <affine> ([∗list] m ∈ ls, Mframe m m)%I
      |-- (Forall x, [| match x.1 with
                        | Normal x => length x = length ls
                        | _ => True
                        end |] -* Q x -* Q' x) -*
          eval oe ls Q -* eval oe ls Q'.
  Proof.
    destruct oe; intros.
    - rewrite /=/nd_seqs. iIntros "A B".
      iApply (nd_seqs'_frame_strong with "B A"). done.
    - simpl.
      destruct ls; simpl.
      { iIntros "_ X"; iApply "X". done. }
      { iIntros "[X Y] K".
        rewrite bi.affinely_elim.
        iApply "X". iIntros (?).
        rewrite /Kbind/Kbind_inner/KP/=.
        case_match; case_match; try iApply "K"; eauto.
        iApply (nd_seqs'_frame_strong with "[K] Y"); eauto.
        iIntros (??) => /=.
        destruct x.1; simpl; iApply "K"; simpl; eauto. }
    - simpl.
      iIntros "X K".
      rewrite /Mmap. iApply (seqs_frame_strong with "[X]").
      { iStopProof. induction ls; simpl; eauto.
        iIntros "[$ K]".
        iDestruct (IHls with "K") as "$". eauto. }
      { iIntros (??); iApply "K".
        destruct x.1; simpl in *; eauto.
        iPureIntro. revert H.
        rewrite !length_rev. eauto. }
  Qed.
End with_cpp.
End cpp_m.

Module Type EVALUATION.
Section with_cpp.
  Context `{Σ : cpp_logic}.

  Import cpp_m.

  (* The expressions in the C++ language are categorized into five
   * "value categories" as defined in:
   *    http://eel.is/c++draft/expr.prop#basic.lval-1
   *
   * - "A glvalue is an expression whose evaluation determines the identity of
   *    an object or function."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.1
   * - "A prvalue is an expression whose evaluation initializes an object or
   *    computes the value of an operand of an operator, as specified by the
   *    context in which it appears, or an expression that has type cv void."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.2
   * - "An xvalue is a glvalue that denotes an object whose resources can be
   *    reused (usually because it is near the end of its lifetime)."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.3
   * - "An lvalue is a glvalue that is not an xvalue."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.4
   * - "An rvalue is a prvalue or an xvalue."
   *   http://eel.is/c++draft/expr.prop#basic.lval-1.5
   *)

  (** lvalues *)
  (* BEGIN wp_lval *)
  (* [wp_lval σ E ρ e Q] evaluates the expression [e] in region [ρ]
   * with mask [E] and continutation [Q].
   *)
  Parameter wp_lval
    : forall {resolve:genv}, translation_unit -> region -> Expr -> M ptr.
  (* END wp_lval *)


  Axiom wp_lval_shift : forall {σ:genv} tu ρ e Q,
      (|={top}=> wp_lval tu ρ e (|={top}=> Q))
    ⊢ wp_lval tu ρ e Q.

  (* Proposal (the same thing for [wp_xval])
     - this would require [has_type (Tref $ Tnamed x) (Vref r)] ~ [strict_valid_ptr r ** [| aligned (Tnamed x) .. |]]
     - this would require [has_type (Tref $ Tarray x n) (Vptr r)] ~ [strict_valid_ptr r ** [| aligned x r |]]
                                                                     ^^^^^^^^^^^^^^^^^^ - just [valid_ptr] if [n = 0]?
     ^^^^ this is questionable because of materialized references

     Consider
     <<
     struct X {};
     struct C {
        int a;
        int& b;
        int&& c;
        X d;
        X& e;
        X&& f;
        X g[1];
        X& g[1];
     }
     >>

     * [primR_observe_has_type] states: [primR ty q v |-- has_type v ty].
       We use [primR (Tref ty) q v] to materialize a reference.
     It would be nice if we had [p |-> primR ty q v |-- has_type (Vref p) (Tref ty)], but this
     will only work when [ty] is not a reference type (potentially also <<void>>).

     we need.
     - [has_type (Vref r) (Tref ty) -|- [strict_valid_ptr r ** aligned_ptr_ty ty r]
       (this rule has a problem with function references because there is no alignment for functions)
       Two options:
       1. functions have 1 alignment
       2. there is a special rule for [has_type  (Vref r) (Tref (Tfunction ..))] that ignores this
     -
   *)
  Axiom wp_lval_well_typed : forall {σ:genv} tu ρ e Q,
      wp_lval tu ρ e (Kbind (fun v k => reference_to (type_of e) v -* k (Normal v, FreeTemps.id)) Q)
    ⊢ wp_lval tu ρ e Q.

  Axiom wp_lval_models : forall {σ:genv} tu ρ e Q,
      denoteModule tu -* wp_lval tu ρ e Q
    ⊢ wp_lval tu ρ e Q.

  Axiom wp_lval_frame : forall σ tu1 tu2 ρ e,
      sub_module tu1 tu2 ->
      |-- Mframe (@wp_lval σ tu1 ρ e) (@wp_lval σ tu2 ρ e).

  Section wp_lval_proper.
    Context {σ : genv}.

    #[local] Notation PROPER M R :=
      (Proper (M ==> eq ==> eq ==> R ==> R) (@wp_lval σ)) (only parsing).

    #[global] Declare Instance wp_lval_ne : forall n, PROPER eq (dist n).

    #[global] Instance wp_lval_mono : PROPER sub_module (⊢).
    Proof.
      repeat red. intros; subst.
      iIntros "X". iRevert "X".
      iApply wp_lval_frame; eauto.
      iIntros (v). iApply H2.
    Qed.

    #[global] Instance wp_lval_flip_mono : PROPER (flip sub_module) (flip (⊢)).
    Proof. repeat intro. red. apply: wp_lval_mono; eauto. Qed.

    #[global] Instance wp_lval_proper : PROPER eq (⊣⊢).
    Proof.
      do 12 intro; subst.
      split'; apply wp_lval_mono; try rewrite H2; done.
    Qed.
  End wp_lval_proper.

  Section wp_lval.
    Context {σ : genv} (tu : translation_unit) (ρ : region) (e : Expr).
    #[local] Notation WP := (wp_lval tu ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : Kpred ptr.

    Lemma wp_lval_wand Q1 Q2 : WP Q1 |-- (∀ v, Q1 v -* Q2 v) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_lval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_lval Q : (|={top}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_lval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_lval_wand with "Hwp").
      setoid_rewrite monPred_at_fupd; eauto.
    Qed.
    Lemma wp_lval_fupd Q : WP (|={top}=> Q) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_lval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_lval p P Q :
      ElimModal True p false (|={top}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_lval.
    Qed.
    #[global] Instance elim_modal_bupd_wp_lval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_lval.
    Qed.
    #[global] Instance add_modal_fupd_wp_lval P Q : AddModal (|={top}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_lval.
    Qed.
  End wp_lval.

  (** * prvalue *)
  (*
   * there are two distinct weakest pre-conditions for this corresponding to the
   * standard text:
   * "A prvalue is an expression whose evaluation...
   * 1. initializes an object, or
   * 2. computes the value of an operand of an operator,
   * as specified by the context in which it appears,..."
   *)

  (* BEGIN wp_init *)
  (* evaluate a prvalue that "initializes an object".

     [wp_init tu ρ ty p e Q] evaluates [e] to initialize a value of type [ty]
     at location [p] in the region [ρ]. The continuation [Q] is passed the
     [FreeTemps.t] needed to destroy temporaries created while evaluating [e],
     but does *not* include the destruction of [p].
     The type [ty] and the type of the expression, i.e. [type_of e], are related
     but not always the same. We call [ty] the *dynamic type* and [type_of e]
     the *static type*. The two types should always be compatible, but the dynamic
     type might have more information. For example, in the expression:
     [[
     int n = 7;
     auto p = new C[n]{};
     ]]
     When running the initializer to initialize the memory returned by [new],
     the dynamic type will be [Tarray "C" 7], while the static type will be
     [Tarray "C" 0] (the [0] is an artifact of clang).

     The memory that is being initialized is already owned by the C++ abstract
     machine. Therefore, schematically, a [wp_init ty addr e Q] looks like the
     following: [[ addr |-> R ... 1 -* Q ]] This choice means that a thread
     needs to give up the memory to the abstract machine when it transitions to
     running a [wp_init]. In the case of stack allocation, there is nothing to
     do here, but in the case of [new], the memory must be given up.

     The C++ standard has many forms of initialization (see
     <https://eel.is/c++draft/dcl.init>). The Clang frontend (and therefore our
     AST) implements the different forms of initialization through elaboration.

     For example, in aggregate pass-by-value the standard states that copy
     initialization <https://eel.is/c++draft/dcl.init#general-14> is used;
     however, the BRiCk AST contains an explicit [Econstructor] in the AST to
     represent this. This seems necessary to have a uniform representation of
     the various evoluations of initialization between different standards, e.g.
     C++14, C++17, etc.

     NOTE: this is morally [M unit], but we inline the definition of [M] and
     ellide the [unit] value. *)
  Parameter wp_init
    : forall {resolve:genv}, translation_unit -> region ->
                        exprtype -> ptr -> Expr ->
                        M FreeTemps.t.
  (* END wp_init *)

  Axiom wp_init_shift : forall {σ:genv} tu ρ ty p e Q,
      (|={top}=> wp_init tu ρ ty p e (|={top}=> Q))
    ⊢ wp_init tu ρ ty p e Q.

  Axiom wp_init_models : forall {σ:genv} tu ty ρ p e Q,
      denoteModule tu -* wp_init tu ρ ty p e Q
    ⊢ wp_init tu ρ ty p e Q.

  Axiom wp_init_well_typed : forall {σ:genv} tu ty ρ p e Q,
      wp_init tu ρ ty p e (Kbind (fun free K => reference_to ty p -* K (Normal free, FreeTemps.id)) Q)
    ⊢ wp_init tu ρ ty p e Q.

  Axiom wp_init_frame : forall σ tu1 tu2 ρ ty p e,
      sub_module tu1 tu2 ->
      |-- Mframe (@wp_init σ tu1 ρ ty p e) (@wp_init σ tu2 ρ ty p e).

  (**
  Separate from [wp_init_frame] because it'll likely have to be proved
  separately (by induction on the type equivalence).
  *)
  Axiom wp_init_type_equiv : forall (σ : genv) tu ρ ty1 ty2 p e Q,
    ty1 ≡ ty2 -> wp_init tu ρ ty1 p e Q -|- wp_init tu ρ ty2 p e Q.

  Section wp_init_proper.
    Context {σ : genv}.

    #[local] Notation PROPER T R := (
      Proper (
        T ==> eq ==> equiv ==> eq ==> eq ==>
        R ==> R
      ) (@wp_init σ)
    ) (only parsing).

    #[global] Declare Instance wp_init_ne : forall n, PROPER eq (dist n).

    #[global] Instance wp_init_mono : PROPER sub_module bi_entails.
    Proof.
      intros tu1 tu2 ? ρ?<- t1 t2 Ht p?<- e?<- Q1 Q2 HQ. iIntros "wp".
      iApply wp_init_type_equiv; [done|].
      iApply (wp_init_frame with "[] wp"); [done|]. iIntros (?).
      iApply HQ.
    Qed.

    #[global] Instance wp_init_flip_mono : PROPER (flip sub_module) (flip bi_entails).
    Proof. repeat intro. exact: wp_init_mono. Qed.

    #[global] Instance wp_init_proper : PROPER eq equiv.
    Proof.
      intros tu?<- ρ?<- t1 t2 Ht p?<- e?<- Q1 Q2 HQ.
      split'; apply wp_init_mono; try done.
      all: by rewrite HQ.
    Qed.
  End wp_init_proper.

  Section wp_init.
    Context {σ : genv} (tu : translation_unit) (ρ : region) (ty : type) (p : ptr) (e : Expr).
    #[local] Notation WP := (wp_init tu ρ ty p e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : Kpred FreeTemps.

    Lemma wp_init_wand Q1 Q2 : WP Q1 |-- (∀ fs, Q1 fs -* Q2 fs) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_init_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_init Q : (|={top}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_init_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_init_wand with "Hwp"). auto.
      setoid_rewrite monPred_at_fupd; eauto.
    Qed.
    Lemma wp_init_fupd Q : WP (|={top}=> Q) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_init_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_init q P Q :
      ElimModal True q false (|={top}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_init.
    Qed.
    #[global] Instance elim_modal_bupd_wp_init q P Q :
      ElimModal True q false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_init.
    Qed.
    #[global] Instance add_modal_fupd_wp_init P Q : AddModal (|={top}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_init.
    Qed.
  End wp_init.

  (* BEGIN wp_prval *)
  Definition wp_prval {resolve:genv} (tu : translation_unit) (ρ : region)
             (e : Expr) (Q : Kpred ptr) : mpred :=
    ∀ p : ptr, wp_init tu ρ (type_of e) p e (Kbind (fun free K => K (Normal p, free)) Q).
  (* END wp_prval *)

  #[global] Instance wp_prval_ne : forall σ n,
    Proper (eq ==> eq ==> eq ==> dist n ==> dist n) (@wp_prval σ).
  Proof. (* solve_proper. Qed. *) Admitted. (* TODO: missing [Proper] instances for [dist n] *)

  (** TODO prove instances for [wp_prval] *)

  (* BEGIN wp_operand *)
  (* evaluate a prvalue that "computes the value of an operand of an operator"
   *)
  Parameter wp_operand : forall {resolve:genv}, translation_unit -> region -> Expr -> M val.
  (* END wp_operand *)

  Axiom wp_operand_shift : forall {σ:genv} tu ρ e Q,
      (|={top}=> wp_operand tu ρ e (|={top}=> Q))
    ⊢ wp_operand (resolve:=σ) tu ρ e Q.

  Axiom wp_operand_models : forall {σ:genv} tu ρ e Q,
      denoteModule tu -* wp_operand tu ρ e Q
    ⊢ wp_operand tu ρ e Q.

  Axiom wp_operand_frame : forall σ tu1 tu2 ρ e,
      sub_module tu1 tu2 ->
      |-- Mframe (@wp_operand σ tu1 ρ e) (@wp_operand σ tu2 ρ e).

  (** C++ evaluation semantics guarantees that all expressions of type [t] that
      evaluate without UB evaluate to a well-typed value of type [t] *)
  Axiom wp_operand_well_typed : forall {σ : genv} tu ρ e Q,
        wp_operand tu ρ e (Kbind (fun v K => has_type v (type_of e) -* K (Normal v, FreeTemps.id)) Q)
    |-- wp_operand tu ρ e Q.

  Section wp_operand_proper.
    Context {σ : genv}.

    #[local] Notation PROPER M R :=
      (Proper (M ==> eq ==> eq ==> R ==> R) (@wp_operand σ)) (only parsing).

    #[global] Declare Instance wp_operand_ne : forall n, PROPER eq (dist n).

    #[global] Instance wp_operand_mono : PROPER sub_module (⊢).
    Proof.
      repeat red. intros; subst.
      iIntros "X". iRevert "X".
      iApply wp_operand_frame; eauto.
      iIntros (v). iApply H2.
    Qed.

    #[global] Instance wp_operand_flip_mono : PROPER (flip sub_module) (flip (⊢)).
    Proof. repeat intro. red. apply wp_operand_mono => //. Qed.

    #[global] Instance wp_operand_proper : PROPER eq (⊣⊢).
    Proof.
      do 12 intro; subst.
      split'; apply wp_operand_mono; try done.
      all: by rewrite H2.
    Qed.
  End wp_operand_proper.

  Section wp_operand.
    Context {σ : genv} (tu : translation_unit) (ρ : region) (e : Expr).
    #[local] Notation WP := (wp_operand tu ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : Kpred val.

    Lemma wp_operand_wand Q1 Q2 : WP Q1 |-- (∀ v, Q1 v -* Q2 v) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_operand_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_operand Q : (|={top}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_operand_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_operand_wand with "Hwp"). auto.
      setoid_rewrite monPred_at_fupd; eauto.
    Qed.
    Lemma wp_operand_fupd Q : WP (|={top}=> Q) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_operand_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_operand p P Q :
      ElimModal True p false (|={top}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_operand.
    Qed.
    #[global] Instance elim_modal_bupd_wp_operand p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_operand.
    Qed.
    #[global] Instance add_modal_fupd_wp_operand P Q : AddModal (|={top}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_operand.
    Qed.
  End wp_operand.

  (** ** boolean operands *)

  (** [wp_test ρ e Q] evaluates [e] as an operand converting the value to a
      boolean before passing it to [Q].
   *)
  Definition wp_test {σ : genv} (tu : translation_unit)  (ρ : region) (e : Expr) : M bool :=
    fun K => wp_operand tu ρ e (Kpure (fun v K => match is_true v with
                                            | Some c => K c
                                            | None => ERROR (is_true_None v)
                                            end) K).
  #[global] Hint Opaque wp_test : br_opacity.
  #[global] Arguments wp_test /.

  #[global] Instance wp_test_ne : forall σ n,
    Proper (eq ==> eq ==> eq ==> dist n ==> dist n) (@wp_test σ).
  Proof. (* solve_proper. Qed. *) Admitted. (* TODO: dist instances. Also, [dist n] for [M] *)

  Lemma wp_test_frame {σ : genv} tu1 tu2 ρ test :
    sub_module tu1 tu2 ->
    |-- Mframe (wp_test tu1 ρ test) (wp_test tu2 ρ test).
  Proof.
    rewrite /wp_test/Mframe. intros.
    iIntros (??) "Q".
    iApply wp_operand_frame; first eauto.
    iIntros (?).
    rewrite /Kbind/Kbind_inner/=.
    repeat case_match; eauto.
    iIntros "[]".
  Qed.

  (** * xvalues *)

  (* evaluate an expression as an xvalue *)
  Parameter wp_xval
    : forall {resolve:genv}, translation_unit -> region -> Expr -> M ptr.

  Axiom wp_xval_shift : forall {σ:genv} tu ρ e Q,
      (|={top}=> wp_xval tu ρ e (|={top}=> Q))
    ⊢ wp_xval tu ρ e Q.

  Axiom wp_xval_models : forall {σ:genv} tu ρ e Q,
      denoteModule tu -* wp_xval tu ρ e Q
    ⊢ wp_xval tu ρ e Q.

  Axiom wp_xval_frame : forall σ tu1 tu2 ρ e,
      sub_module tu1 tu2 ->
      |-- Mframe (@wp_xval σ tu1 ρ e) (@wp_xval σ tu2 ρ e).

  Section wp_xval_proper.
    Context {σ : genv}.

    #[local] Notation PROPER M R :=
      (Proper (M ==> eq ==> eq ==> R ==> R) wp_xval) (only parsing).

    #[global] Declare Instance wp_xval_ne n : PROPER eq (dist n).

    #[global] Instance wp_xval_mono : PROPER sub_module (⊢).
    Proof.
      repeat red. intros; subst.
      iIntros "X". iRevert "X".
      iApply wp_xval_frame; eauto.
      iIntros (v). iApply H2 => //.
    Qed.

    #[global] Instance wp_xval_flip_mono : PROPER (flip sub_module) (flip (⊢)).
    Proof. repeat intro. red. rewrite wp_xval_mono => // ????; apply H2 => //. Qed.

    #[global] Instance wp_xval_proper : PROPER eq (⊣⊢).
    Proof.
      do 12 intro; subst.
      split'; apply wp_xval_mono; try done.
      all: by rewrite H2.
    Qed.
  End wp_xval_proper.

  Section wp_xval.
    Context {σ : genv} (tu : translation_unit) (ρ : region) (e : Expr).
    #[local] Notation WP := (wp_xval tu ρ e) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : Kpred ptr.

    Lemma wp_xval_wand Q1 Q2 : WP Q1 |-- (∀ v, Q1 v -* Q2 v) -* WP Q2.
    Proof. iIntros "Hwp HK". by iApply (wp_xval_frame with "HK Hwp"). Qed.
    Lemma fupd_wp_xval Q : (|={top}=> WP Q) |-- WP Q.
    Proof.
      rewrite -{2}wp_xval_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_xval_wand with "Hwp"). auto.
      setoid_rewrite monPred_at_fupd; eauto.
    Qed.
    Lemma wp_xval_fupd Q : WP (|={top}=> Q) |-- WP Q.
    Proof. iIntros "Hwp". by iApply (wp_xval_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_xval p P Q :
      ElimModal True p false (|={top}=> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_xval.
    Qed.
    #[global] Instance elim_modal_bupd_wp_xval p P Q :
      ElimModal True p false (|==> P) P (WP Q) (WP Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_xval.
    Qed.
    #[global] Instance add_modal_fupd_wp_xval P Q : AddModal (|={top}=> P) P (WP Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_xval.
    Qed.
  End wp_xval.

  (* Opaque wrapper of [False]: this represents a [False] obtained by a [ValCat] mismatch in [wp_glval]. *)
  Definition wp_glval_mismatch {resolve : genv} (r : region) (vc : ValCat) (e : Expr)
    : M ptr := funI _ => |={top}=> False.
  #[global] Arguments wp_glval_mismatch : simpl never.

  (* evaluate an expression as a generalized lvalue *)

  (* In some cases we need to evaluate a glvalue.
     This makes some weakest pre-condition axioms a bit shorter.
   *)
  Definition wp_glval {σ} (tu : translation_unit) ρ (e : Expr) : M ptr :=
      match valcat_of e with
      | Lvalue => wp_lval (resolve:=σ) tu ρ e
      | Xvalue => wp_xval (resolve:=σ) tu ρ e
      | vc => wp_glval_mismatch ρ vc e
      end%I.

  #[global] Instance wp_glval_ne σ n :
    Proper (eq ==> eq ==> eq ==> dist n ==> dist n) (@wp_glval σ).
  Proof.
    do 12 intro. rewrite /wp_glval; subst.
    case_match; try solve_proper.
  Qed.

  (**
  Note:

  - [wp_glval_shift] and [fupd_wp_glval] are not sound without a later
  credit in the [Prvalue] case

  - [wp_glval_models] isn't sound without [denoteModule tu] in the
  [Prvalue] case
  *)

  Lemma wp_glval_frame {σ : genv} tu1 tu2 r e :
    sub_module tu1 tu2 ->
    |-- Mframe (wp_glval tu1 r e) (wp_glval tu2 r e).
  Proof.
    rewrite /wp_glval. case_match.
    - by apply wp_lval_frame.
    - admit. (* TODO *)
    - by apply wp_xval_frame.
  Admitted. (* TODO *)

  #[global] Instance Proper_wp_glval σ :
    Proper (sub_module ==> eq ==> eq ==> Mrel _) (@wp_glval σ).
  Proof.
    solve_proper_prepare. case_match; try solve_proper.
  Qed.

  Section wp_glval.
    Context {σ : genv} (tu : translation_unit) (ρ : region).
    #[local] Notation wp_glval := (wp_glval tu ρ) (only parsing).
    #[local] Notation wp_lval := (wp_lval tu ρ) (only parsing).
    #[local] Notation wp_xval := (wp_xval tu ρ) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : Kpred ptr.

    Lemma wp_glval_lval e Q :
      valcat_of e = Lvalue -> wp_glval e Q -|- wp_lval e Q.
    Proof. by rewrite /wp_glval=>->. Qed.

    Lemma wp_glval_xval e Q :
      valcat_of e = Xvalue -> wp_glval e Q -|- wp_xval e Q.
    Proof. by rewrite /wp_glval=>->. Qed.

    Lemma wp_glval_prval e Q :
      valcat_of e = Prvalue -> wp_glval e Q -|- |={top}=> False.
    Proof. by rewrite /wp_glval=>->. Qed.

    Lemma wp_glval_wand e Q Q' :
      wp_glval e Q |-- (Forall v, Q v -* Q' v) -* wp_glval e Q'.
    Proof.
      iIntros "A B". iRevert "A". by iApply wp_glval_frame.
    Qed.

    Lemma fupd_wp_glval e Q :
      (|={top}=> wp_glval e Q) |-- wp_glval e Q.
    Proof.
      rewrite /wp_glval/wp_glval_mismatch. case_match;
        auto using fupd_wp_lval, fupd_wp_xval.
      by iIntros ">>$".
    Qed.

    Lemma wp_glval_fupd e Q :
      wp_glval e (|={top}=> Q) |-- wp_glval e Q.
    Proof.
      rewrite /wp_glval/wp_glval_mismatch. case_match;
      auto using wp_lval_fupd, wp_xval_fupd.
    Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_glval p e P Q :
      ElimModal True p false (|={top}=> P) P (wp_glval e Q) (wp_glval e Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_glval.
    Qed.
    #[global] Instance elim_modal_bupd_wp_glval p e P Q :
      ElimModal True p false (|==> P) P (wp_glval e Q) (wp_glval e Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_glval.
    Qed.
    #[global] Instance add_modal_fupd_wp_glval e P Q : AddModal (|={top}=> P) P (wp_glval e Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_glval.
    Qed.

  End wp_glval.

  (** Discarded values.

      Sometimes expressions are evaluated only for their side-effects.
      https://eel.is/c++draft/expr#context-2

      The definition [wp_discard] captures this and allows us to express some
      rules more concisely. The value category used to evaluate the expression
      is computed from the expression using [valcat_of].
   *)
  Section wp_discard.
    Context {σ : genv} (tu : translation_unit).
    Variable (ρ : region).

    Definition wp_discard (e : Expr) : M unit :=
      fun K =>
        match valcat_of e with
        | Lvalue => wp_lval tu ρ e (Kpure (fun _ K => K ()) K)
        | Prvalue =>
            let ty := type_of e in
            if is_value_type ty then
              wp_operand tu ρ e (Kpure (fun _ K => K ()) K)
            else
              Forall p, wp_init tu ρ (type_of e) p e (Kbind (fun free K => K (Normal (), free)) K)
        | Xvalue => wp_xval tu ρ e (Kpure (fun _ K => K ()) K)
        end.

    Lemma fupd_wp_discard e Q :
      (|={top}=> wp_discard e Q) |-- wp_discard e Q.
    Proof.
      rewrite /wp_discard. repeat case_match; iIntros  ">$".
    Qed.

    Lemma wp_discard_fupd e Q :
      wp_discard e (|={top}=> Q) |-- wp_discard e Q.
    Proof.
      rewrite /wp_discard. repeat case_match;
        auto using wp_lval_fupd, wp_xval_fupd, wp_operand_fupd.
      (*
      f_equiv; intro; auto using wp_init_fupd.
    Qed. *) Admitted.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp_discard p e P Q :
      ElimModal True p false (|={top}=> P) P (wp_discard e Q) (wp_discard e Q).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_discard.
    Qed.
    #[global] Instance elim_modal_bupd_wp_discard p e P Q :
      ElimModal True p false (|==> P) P (wp_discard e Q) (wp_discard e Q).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp_discard.
    Qed.
    #[global] Instance add_modal_fupd_wp_discard e P Q : AddModal (|={top}=> P) P (wp_discard e Q).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp_discard.
    Qed.

  End wp_discard.

  #[global] Instance wp_discard_ne σ n :
    Proper (eq ==> eq ==> eq ==> dist n ==> dist n) (@wp_discard σ).
  Proof. (* solve_proper. Qed. *) Admitted. (* TODO *)

  Lemma wp_discard_frame {σ : genv} tu1 tu2 ρ e :
    sub_module tu1 tu2 ->
    |-- Mframe (wp_discard tu1 ρ e) (wp_discard tu2 ρ e).
  Proof. (*
    rewrite /wp_discard.
    destruct (valcat_of e) => /=.
    - intros. rewrite -wp_lval_frame; eauto.
      iIntros "h" (v f) "x"; iApply "h"; iFrame.
    - intros. case_match.
      + iIntros "h"; iApply wp_operand_frame; eauto.
        iIntros (??); iApply "h".
      + iIntros "a b" (p).
        iSpecialize ("b" $! p).
        iRevert "b"; iApply wp_init_frame; eauto.
        iIntros (?); iApply "a".
    - intros. rewrite -wp_xval_frame; eauto.
      iIntros "h" (v f) "x"; iApply "h"; iFrame.
  Qed. *) Admitted.

  #[global] Instance wp_discard_mono σ :
    Proper (sub_module ==> eq ==> eq ==> (⊢) ==> (⊢))
           (@wp_discard σ).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wp_discard_frame; eauto.
    iIntros (?); iApply H2; reflexivity.
  Qed.

  #[global] Instance wp_discard_flip_mono σ :
    Proper (flip sub_module ==> eq ==> eq ==> flip (⊢) ==> flip (⊢))
           (@wp_discard σ).
  Proof. solve_proper. Qed.

  (** * Statements *)

  (* evaluate a statement *)
  Parameter wp
    : forall {resolve:genv}, translation_unit -> region -> Stmt -> Kpred () -> mpred.

  #[global] Declare Instance wp_ne : forall σ n,
    Proper (eq ==> eq ==> eq ==> dist n ==> dist n) (@wp σ).

  Axiom wp_shift : forall σ tu ρ s Q,
      (|={top}=> wp tu ρ s (|={top}=> Q))
    ⊢ wp (resolve:=σ) tu ρ s Q.

  Axiom wp_models : forall σ tu ρ s Q,
      denoteModule tu -* wp tu ρ s Q
    ⊢ wp (resolve:=σ) tu ρ s Q.

  Axiom wp_frame : forall {σ : genv} tu1 tu2 ρ s (k1 k2 : Kpred ()),
      sub_module tu1 tu2 ->
      (Forall rt, k1 rt -* k2 rt) |-- wp tu1 ρ s k1 -* wp tu2 ρ s k2.

  #[global] Instance Proper_wp {σ} :
    Proper (sub_module ==> eq ==> eq ==> (⊢) ==> (⊢))
           (@wp σ).
  Proof.
    repeat red; intros; subst.
    iIntros "X"; iRevert "X"; iApply wp_frame; eauto.
    iIntros (rt). iApply H2.
  Qed.

  Section wp.
    Context {σ : genv} (tu : translation_unit) (ρ : region) (s : Stmt).
    #[local] Notation WP := (wp tu ρ s) (only parsing).
    Implicit Types P : mpred.
    Implicit Types Q : Kpred ().

    Lemma wp_wand (k1 k2 : Kpred ()) :
      WP k1 |-- (Forall rt, k1 rt -* k2 rt) -* WP k2.
    Proof.
      iIntros "Hwp Hk". by iApply (wp_frame _ _ _ _ k1 with "[$Hk] Hwp").
    Qed.
    Lemma fupd_wp k : (|={top}=> WP k) |-- WP k.
    Proof.
      rewrite -{2}wp_shift. apply fupd_elim. rewrite -fupd_intro.
      iIntros "Hwp". iApply (wp_wand with "Hwp").
      iIntros (?) "X". iModIntro; eauto.
    Qed.
    Lemma wp_fupd k : WP (|={top}=> k) |-- WP k.
    Proof. iIntros "Hwp". by iApply (wp_shift with "[$Hwp]"). Qed.

    (* proof mode *)
    #[global] Instance elim_modal_fupd_wp p P k :
      ElimModal True p false (|={top}=> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal. rewrite bi.intuitionistically_if_elim/=.
      by rewrite fupd_frame_r bi.wand_elim_r fupd_wp.
    Qed.
    #[global] Instance elim_modal_bupd_wp p P k :
      ElimModal True p false (|==> P) P (WP k) (WP k).
    Proof.
      rewrite /ElimModal (bupd_fupd top). exact: elim_modal_fupd_wp.
    Qed.
    #[global] Instance add_modal_fupd_wp P k : AddModal (|={top}=> P) P (WP k).
    Proof.
      rewrite/AddModal. by rewrite fupd_frame_r bi.wand_elim_r fupd_wp.
    Qed.
  End wp.

  (* this is the low-level specification of C++ functions.
   *
   * [addr] represents the address of the entry point of the code.
   * note: the [list ptr] will be related to the register set.
   *
   * TODO: Ideally, I would use [Kpred ptr] here, but the only
   *       valid results are [Normal p] or [Throw ty p].
   *)
  Parameter wp_fptr
    : forall (tt : type_table) (fun_type : type) (* TODO: function type *)
        (addr : ptr) (ls : list ptr) (Q : ptr -> mpred), mpred.

  (* (bind [n] last for consistency with [NonExpansive]). *)
  #[global] Declare Instance wp_fptr_ne :
    `{forall n, Proper (pointwise_relation _ (dist n) ==> dist n) (@wp_fptr t ft addr ls)}.

  Axiom wp_fptr_complete_type : forall te ft a ls Q,
      wp_fptr te ft a ls Q
      |-- wp_fptr te ft a ls Q **
          [| exists cc ar tret targs, ft = Tfunction (@FunctionType _ cc ar tret targs) |].

  (* A type is callable against a type table if all of its arguments and return
     type are [complete_type]s.

     This effectively means that there is enough information to determine the
     calling convention.
   *)
  Definition callable_type (tt : type_table) (t : type) : Prop :=
    match t with
    | Tfunction ft => complete_type tt ft.(ft_return) /\ List.Forall (complete_type tt) ft.(ft_params)
    | _ => False
    end.

  (* this axiom states that the type environment for an [wp_fptr] can be
     narrowed as long as the new type environment [small]/[tt2] is smaller than
     the old type environment ([big]/[tt1]), and [ft]
     is still a *complete type* in the new type environment [small]/[tt2].

     NOTE: This is informally justified by the fact that (in the absence
     of ODR) the implementation of the function is encapsulated and only
     the public interface (the type) is needed to know how to call the function.
   *)
  Axiom wp_fptr_strengthen : forall tt1 tt2 ft a ls Q,
      callable_type tt2.(types) ft ->
      sub_module tt2 tt1 ->
      wp_fptr tt1.(types) ft a ls Q |-- wp_fptr tt2.(types) ft a ls Q.

  (* this axiom is the standard rule of consequence for weakest
     pre-condition.
   *)
  Axiom wp_fptr_frame_fupd : forall tt1 tt2 ft a ls Q1 Q2,
      type_table_le tt1 tt2 ->
          (Forall v, Q1 v -* |={top}=> Q2 v)
      |-- @wp_fptr tt1 ft a ls Q1 -* @wp_fptr tt2 ft a ls Q2.

  Lemma wp_fptr_frame : forall tt ft a ls Q1 Q2,
    (Forall v, Q1 v -* Q2 v)
    |-- wp_fptr tt ft a ls Q1 -* wp_fptr tt ft a ls Q2.
  Proof using Σ.
    intros. iIntros "H". iApply wp_fptr_frame_fupd; first reflexivity.
    iIntros (v) "? !>". by iApply "H".
  Qed.

  (* the following two axioms say that we can perform fupd's
     around the weakeast pre-condition. *)
  Axiom wp_fptr_fupd : forall te ft a ls Q,
      wp_fptr te ft a ls (λ v, |={top}=> Q v) |-- wp_fptr te ft a ls Q.
  Axiom fupd_spec : forall te ft a ls Q,
      (|={top}=> wp_fptr te ft a ls Q) |-- wp_fptr te ft a ls Q.

  Lemma wp_fptr_shift te ft a ls Q :
    (|={top}=> wp_fptr te ft a ls (λ v, |={top}=> Q v)) |-- wp_fptr te ft a ls Q.
  Proof.
    by rewrite fupd_spec wp_fptr_fupd.
  Qed.

  #[global] Instance Proper_wp_fptr : forall tt ft a ls,
      Proper (pointwise_relation _ lentails ==> lentails) (@wp_fptr tt ft a ls).
  Proof using Σ.
    repeat red; intros.
    iApply wp_fptr_frame.
    iIntros (v); iApply H.
  Qed.

  Section wp_fptr.
    Context {tt : type_table} {tf : type} (addr : ptr) (ls : list ptr).
    #[local] Notation WP := (wp_fptr tt tf addr ls) (only parsing).
    Implicit Types Q : ptr → mpred.

    Lemma wp_fptr_wand_fupd Q1 Q2 : WP Q1 |-- (∀ v, Q1 v -* |={top}=> Q2 v) -* WP Q2.
    Proof.
      iIntros "Hwp HK".
      iApply (wp_fptr_frame_fupd with "HK Hwp").
      reflexivity.
    Qed.

    Lemma wp_fptr_wand Q1 Q2 : WP Q1 |-- (∀ v, Q1 v -* Q2 v) -* WP Q2.
    Proof using Σ.
      iIntros "Hwp HK".
      iApply (wp_fptr_frame with "HK Hwp").
    Qed.
  End wp_fptr.

  (** [wp_mfptr tt this_ty fty ..] is the analogue of [wp_fptr] for member functions.

      NOTE this includes constructors and destructors.

      NOTE the current implementation desugars this to [wp_fptr] but this is not
           accurate according to the standard because a member function can not
           be cast to a regular function that takes an extra parameter.
           We could fix this by splitting [wp_fptr] more, but we are deferring that
           for now.

           In practice we assume that the AST is well-typed, so the only way to
           exploit this is to use [reinterpret_cast< >] to cast a function pointer
           to an member pointer or vice versa.
   *)
  Definition wp_mfptr (tt : type_table) (this_type : exprtype) (fun_type : functype)
    : ptr -> list ptr -> (ptr -> mpred) -> mpred :=
    wp_fptr tt (Tmember_func this_type fun_type).

  (* (bind [n] last for consistency with [NonExpansive]). *)
  #[global] Declare Instance wp_mfptr_ne :
    `{forall n, Proper (pointwise_relation _ (dist n) ==> dist n) (@wp_mfptr t ft addr this ls)}.

  Lemma wp_mfptr_frame_fupd_strong tt1 tt2 t t0 v l Q1 Q2 :
    type_table_le tt1 tt2 ->
    (Forall v, Q1 v -* |={top}=> Q2 v)
    |-- wp_mfptr tt1 t t0 v l Q1 -* wp_mfptr tt2 t t0 v l Q2.
  Proof. apply wp_fptr_frame_fupd. Qed.

  Lemma wp_mfptr_shift tt t t0 v l Q :
    (|={top}=> wp_mfptr tt t t0 v l (λ v, |={top}=> Q v)) |-- wp_mfptr tt t t0 v l Q.
  Proof. apply wp_fptr_shift. Qed.

  Lemma wp_mfptr_frame:
    ∀ (t : type) (l : list ptr) (v : ptr) (t0 : type) (t1 : type_table) (Q Q' : ptr -> _),
      Forall v, Q v -* Q' v |-- wp_mfptr t1 t t0 v l Q -* wp_mfptr t1 t t0 v l Q'.
  Proof using Σ. intros; apply wp_fptr_frame. Qed.

  Lemma wp_mfptr_frame_fupd :
    ∀ (t : type) (l : list ptr) (v : ptr) (t0 : type) (t1 : type_table) (Q Q' : ptr -> _),
      (Forall v, Q v -* |={top}=> Q' v) |-- wp_mfptr t1 t t0 v l Q -* wp_mfptr t1 t t0 v l Q'.
  Proof using Σ. intros; apply wp_fptr_frame_fupd; reflexivity. Qed.

End with_cpp.

(** Forbid rewriting in the [`{Σ : cpp_logic, σ : genv}] arguments.
Keep in sync with [Proper] instances. *)
#[global] Instance: Params (@wp_lval) 4 := {}.
#[global] Instance: Params (@wp_init) 4 := {}.
#[global] Instance: Params (@wp_prval) 4 := {}.
#[global] Instance: Params (@wp_operand) 4 := {}.
#[global] Instance: Params (@wp_test) 4 := {}.
#[global] Instance: Params (@wp_xval) 4 := {}.
#[global] Instance: Params (@wp_glval) 4 := {}.
#[global] Instance: Params (@wp_discard) 4 := {}.
#[global] Instance: Params (@wp) 4 := {}.

(** Also forbid rewriting in the extra arguments except the continuation.
Keep in sync with [Proper] instances.
TODO: maybe be more uniform in the future. *)
#[global] Instance: Params (@wp_fptr) 7 := {}.
#[global] Instance: Params (@wp_mfptr) 8 := {}.

(* DEPRECATIONS *)
#[deprecated(since="20241102",note="use [wp_mfptr].")]
Notation mspec := wp_mfptr.
#[deprecated(since="20241102",note="use [wp_mfptr_frame_fupd_strong].")]
Notation mspec_frame_fupd_strong := wp_mfptr_frame_fupd_strong.
#[deprecated(since="20241102",note="use [wp_mfptr_shift].")]
Notation mspec_shift := wp_mfptr_shift.
#[deprecated(since="20241102",note="use [wp_mfptr_frame].")]
Notation mspec_frame := wp_mfptr_frame.
#[deprecated(since="20241102",note="use [wp_mfptr_frame].")]
Notation mspec_frame_fupd := wp_mfptr_frame_fupd.
End EVALUATION.

Declare Module evaluation : EVALUATION.
Export cpp_m.
Export evaluation.
Export stdpp.coPset.
