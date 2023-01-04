(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

From iris.algebra Require Import cmra frac.
From bedrock.prelude Require Import bool.
From bedrock.lang.bi Require Import split_frac.

#[local] Set Printing Coercions.

(* TODO: the name here probably does not make sense anymore *)
Module cQp.

  #[projections(primitive)]
  Record t : Set := mk { is_const : bool ; frac : Qp }.
  Add Printing Constructor t.

  Lemma eta q : q = mk q.(is_const) q.(frac).
  Proof. done. Qed.

  #[global] Instance t_inhabited : Inhabited t.
  Proof. apply populate, mk; apply inhabitant. Qed.
  #[global] Instance t_eq_dec : EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance t_countable : Countable t.
  Proof.
    apply (inj_countable'
      (fun x => (x.(is_const), x.(frac)))
      (fun p => mk p.1 p.2)).
    abstract (by intros []).
  Defined.

  Canonical Structure tO : ofe := leibnizO t.

  #[global] Instance: Params mk 0 := {}.
  #[global] Instance mk_ne : NonExpansive2 mk.
  Proof.
    intros n. by do 2!(intros ??; rewrite -discrete_iff leibniz_equiv_iff=>->).
  Qed.
  #[global] Instance mk_proper : Proper (equiv ==> equiv ==> equiv) mk.
  Proof. exact: ne_proper_2. Qed.

  #[global] Instance: Params is_const 0 := {}.
  #[global] Instance is_const_ne : NonExpansive is_const := _.
  #[global] Instance is_const_proper : Proper (equiv ==> equiv) is_const := _.

  #[global] Instance: Params frac 0 := {}.
  #[global] Instance frac_ne : NonExpansive frac := _.
  #[global] Instance frac_proper : Proper (equiv ==> equiv) frac := _.

  #[global] Instance mk_inj_eq : Inj2 eq eq eq mk.
  Proof. by intros ???? [= ->->]. Qed.
  #[global] Instance mk_inj_equiv : Inj2 equiv equiv equiv mk.
  Proof. intros ????. fold_leibniz. apply mk_inj_eq. Qed.
  #[global] Instance mk_inj_dist n : Inj2 (dist n) (dist n) (dist n) mk.
  Proof. intros ????. rewrite -!discrete_iff. apply mk_inj_equiv. Qed.

  #[global] Hint Opaque is_const frac : typeclass_instances.

  Section cmra.
    #[local] Open Scope bool_scope.
    Implicit Types (x y : t).

    #[local] Notation OP x y :=
      (mk (x.(is_const) && y.(is_const)) (x.(frac) + y.(frac))) (only parsing).
    #[local] Instance t_op_instance : Op t := fun x y => OP x y.
    #[local] Instance t_pcore_instance : PCore t := fun x => None.
    #[local] Instance t_valid_instance : Valid t := fun x => ✓ x.(frac).

    Lemma t_op x y : x ⋅ y = OP x y.
    Proof. done. Qed.
    Lemma t_op_op x y : x ⋅ y = mk (x.(is_const) && y.(is_const)) (x.(frac) ⋅ y.(frac)).
    Proof. done. Qed.
    Lemma t_pcore x : pcore x = None.
    Proof. done. Qed.
    Lemma t_valid x : ✓ x = ✓ x.(frac).
    Proof. done. Qed.
    Lemma t_included x y :
      x ≼ y <-> y.(is_const) <= x.(is_const) /\ (x.(frac) < y.(frac))%Qp.
    Proof.
      rewrite -frac_included. split.
      - intros [z ->%leibniz_equiv]. cbn. split. done. by exists (frac z).
      - intros [? [frac Hfrac]]. exists (mk y.(is_const) frac).
        rewrite t_op_op /=. by rewrite Bool.andb_min_r// -Hfrac.
    Qed.

    #[global] Instance mk_mono : Proper (flip Bool.le ==> Qp.lt ==> (≼)) mk.
    Proof. solve_proper_prepare. by rewrite t_included. Qed.
    #[global] Instance is_const_mono : Proper ((≼) ==> flip Bool.le) is_const.
    Proof. by intros x y [??]%t_included. Qed.
    #[global] Instance frac_mono : Proper ((≼) ==> Qp.lt) frac.
    Proof. by intros x y [??]%t_included. Qed.

    Lemma t_ra_mixin : RAMixin t.
    Proof.
      split; first [apply _|done|idtac].
      - (** ra_assoc *) intros x y z. by rewrite !t_op !assoc_L.
      - (** ra_comm *) intros x y. rewrite !t_op.
        by rewrite [_ && _]comm_L [(_ + _)%Qp]comm_L.
      - (** ra_valid_op_l *) intros x y. rewrite t_op t_valid /=.
        exact: cmra_valid_op_l.
    Qed.
    Canonical Structure tR : cmra := discreteR t t_ra_mixin.

    #[global] Instance t_cmra_discrete : CmraDiscrete t.
    Proof. split. by apply _. done. Qed.

    #[global] Instance t_exclusive b : Exclusive (mk b 1).
    Proof.
      intros x. rewrite -cmra_discrete_valid_iff t_valid /=.
      exact: exclusive_l.
    Qed.
    #[global] Instance t_id_free x : IdFree x.
    Proof.
      apply: discrete_id_free=>y. rewrite t_valid=>/= Hv.
      rewrite (eta y) t_op=>/= /mk_inj_equiv [] _ Heq.
      exact: (id_free_r x.(frac)).
    Qed.
    #[global] Instance t_cancelable q : Cancelable (mk true q).
    Proof.
      apply: discrete_cancelable=>y z.
      rewrite (eta y) (eta z) !t_op /=.
      rewrite t_valid=>/= Hv. move=>/mk_inj_equiv [] -> Heq. f_equiv.
      exact: (cancelable q).
    Qed.
  End cmra.

  (* scaling *)
  Notation scale q cq := (mk cq.(is_const) (q * cq.(frac))).

  Lemma scale_combine s1 s2 q :
    scale s1 q ⋅ scale s2 q = scale (s1 + s2) q.
  Proof.
    by rewrite /op/cQp.tR/cmra_op/cQp.t_op_instance/=;
       rewrite -Qp.mul_add_distr_r Bool.andb_diag. Qed.
  Lemma scale_1 q : scale 1 q = q.
  Proof. by rewrite Qp.mul_1_l. Qed.

  Notation mut := (mk false).
  Notation m := (mk false) (only parsing).
  Notation const := (mk true).
  Notation c := (mk true) (only parsing).

  Lemma mk_add' c q1 q2 : mk c (q1 + q2) = mk c q1 ⋅ mk c q2.
  Proof. by rewrite t_op /= andb_diag. Qed.

  Lemma mk_add `{!SplitFrac q q1 q2} c : mk c q = mk c q1 ⋅ mk c q2.
  Proof. by rewrite (split_frac q) mk_add'. Qed.

  Lemma mut_const' q1 q2 : mut (q1 + q2) = mut q1 ⋅ const q2.
  Proof. done. Qed.

  Lemma mut_const `{!SplitFrac q q1 q2} : mut q = mut q1 ⋅ const q2.
  Proof. by rewrite (split_frac q). Qed.

  #[deprecated(since="20221223", note="use [cmra.op] or [⋅]")]
  Notation add := (op (A:=t)) (only parsing).
  #[deprecated(since="20221223", note="use [cQp.t_op]")]
  Notation add_eq := t_op (only parsing).

  #[local] Definition _refl (c : bool) (q : Qp) : mk c q = mk c q := eq_refl _.
  #[deprecated(since="20221223")]
  Notation refl := _refl (only parsing).

End cQp.

Add Printing Constructor cQp.t.
Canonical Structure cQp.tO.
Canonical Structure cQp.tR.

(* as with C++, we make mutable the default *)
#[global] Coercion cQp.frac : cQp.t >-> Qp.
#[global] Bind Scope Qp_scope with cQp.t.	(** Complements the [_mut] coercion *)

(** ** Backwards compatibility *)
(**
Old code can benefit from a coercion.
*)
Module cQp_compat.

  Module cQp.
    Export cv.cQp.

    Definition _mut : Qp -> t := mut.
    #[global] Arguments cQp._mut /.
  End cQp.

  Coercion cQp._mut : Qp >-> cQp.t.

End cQp_compat.

Section TEST.
  Variable TEST : cQp.t -> cQp.t -> cQp.t -> cQp.t -> Prop.
  Import cQp_compat.

  (* TODO: to make this work without the [%Qp], we need to register the
     notations for [Qp] as notations in [cvq_scope]. *)
  Goal TEST 1 (cQp.c 1) (1/2) (cQp.c (1/4)).
  Abort.

End TEST.
