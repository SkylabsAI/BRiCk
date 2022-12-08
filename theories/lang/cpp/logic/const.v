(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.bi Require Export monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import iris.bi.lib.fractional.


Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import
  semantics ast logic.pred logic.path_pred logic.rep logic.rep_defs heap_notations
  heap_pred layout logic.wp.


Section defs.
  Context `{Σ : cpp_logic}  {σ : genv}.

  (* [cv_cast from to addr ty Q] replaces the [from] ownership of [ty] at [addr] with
     [to] ownership and then proceeds as [Q].

     This is used to implement [wp_downcast_to_const] and [wp_upcast_to_const].
   *)
  Parameter cv_cast : forall (tu : translation_unit) (from to : CV.t) (addr : ptr) (ty : type) (Q : mpred), mpred.
  Axiom cv_cast_frame : forall f t a ty Q Q',
      Q -* Q' |-- cv_cast tu f t a ty Q -* cv_cast tu f t a ty Q'.

  Definition type_is_const (ty : type) : bool :=
    let '(cv, _) := decompose_type ty in q_const cv.

  (* TODO this needs to be extended because if it is casting [volatile],
     then it needs to descend under [const] *)
  Definition cv_cast_body (cv_cast : forall (from to : CV.t) (addr : ptr) (ty : type) (Q : mpred), mpred)
    (tu : translation_unit) (from to : CV.t)  (addr : ptr) (ty : type) (Q : mpred) : mpred :=
    let '(cv, rty) := decompose_type ty in
    if q_const cv then Q
    else
      let UNSUPPORTED := cv_cast from to addr ty Q in
      match rty with
      | Tptr _
      | Tnum _ _
      | Tbool
      | Tnullptr
      | Tenum _
      | Tmember_pointer _ _
      | Tfloat _
      | Tvoid =>
        let rty := erase_qualifiers rty in
        (Exists v, addr |-> primR rty from v ** (addr |-> primR rty to v -* Q)) ∨
        (          addr |-> uninitR rty from ** (addr |-> uninitR rty to -* Q))

      | Tref _
      | Trv_ref _ =>
        let rty := erase_qualifiers rty in
        (Exists v, addr |-> primR rty from v ** (addr |-> primR rty to v -* Q))
        (* ^ References must be initialized *)

      | Tarray ety sz =>
        (* NOTE the order here is irrelevant because the operation is "atomic" *)
        fold_left (fun Q i =>
            cv_cast from to (addr .[ erase_qualifiers ety ! sz ]) ty Q)
                    (seqN 0 sz) Q

      | Tnamed cls =>
          match tu.(globals) !! cls with
          | Some gd =>
              match gd with
              | Gunion u =>
                Exists br, addr |-> union_paddingR from cls br ** (addr |-> union_paddingR to cls br -*
                match br with
                | None =>  Q
                | Some br => match u.(u_fields) !! br with
                            | None => False
                            | Some m =>
                                if m.(mem_mutable) || type_is_const m.(mem_type)
                                then Q
                                else
                                  cv_cast from to (addr ,, _field {| f_type := cls ; f_name := m.(mem_name) |}) m.(mem_type) Q
                            end
                end)
              | Gstruct st =>
                  fold_left (fun Q '(b, _) =>
                              cv_cast from to (addr ,, _base cls b) (Tnamed b) Q)
                    (s_bases st) $
                    fold_left (fun Q m =>
                                if m.(mem_mutable) || type_is_const m.(mem_type)
                                then Q
                                else cv_cast from to
                                        (addr ,, _field {| f_type := cls; f_name := m.(mem_name) |})
                                        m.(mem_type) Q)
                    (s_fields st)
                    (addr |-> struct_paddingR from cls ** (addr |-> struct_paddingR to cls -* Q))
              | Gtype
              | Genum _ _
              | Gconstant _ _
              | Gtypedef _ => UNSUPPORTED
              end
          | None => UNSUPPORTED
          end
      | Tfunction _ _
      | Tarch _ _ => UNSUPPORTED
      | Tqualified cv ty' => False (* unreachable *)
      end%I.

  (* NOTE: we prefer an entailment ([|--]) to a bi-entailment ([-|-]) or an equality
     to be conservative.
   *)
  Axiom cv_cast_intro : forall tu f t a ty Q, cv_cast_body (cv_cast tu) tu f t a ty Q |-- cv_cast tu f t a ty Q.

  (* Sanity check the [_frame] property *)
  Lemma fold_left_frame : forall B (l : list B) (f f' : epred -> B -> epred)  (Q Q' : epred),
    (Q -* Q') |-- □ (Forall Q1 Q1' a, (Q1 -* Q1') -* (f Q1 a -* f' Q1' a)) -*  fold_left f l Q -* fold_left f' l Q'.
  Proof.
    move=>B l.
    induction l; iIntros (????) "W #F"; first done.
    iDestruct ("F" $! Q Q' a with "W") as "W".
    iApply (IHl with "W"). eauto.
  Qed.

  (* Sanity check *)
  Lemma cv_cast_body_frame_uniform : forall CAST tu q q' p ty (Q Q' : epred),
    Q -* Q'
    |-- □ (Forall a b p ty Q Q', (Q -* Q') -* CAST a b p ty Q -* CAST a b p ty Q') -*
        cv_cast_body CAST tu q q' p ty Q -* cv_cast_body CAST tu q q' p ty Q'.
  Proof.
    rewrite /cv_cast_body/=; intros.
    destruct (decompose_type ty) as [cv t].
    case_match.
    { iIntros "$ _"; eauto. }
    destruct t; eauto.

    (* unsupported *)
    all: try by iIntros "X C"; iApply "C"; eauto.

    (* primitives *)
    all: try solve [ iIntros "F #C X"; iDestruct "X" as "[X | X]";
        [ iLeft; iDestruct "X" as (v) "[? X]"; iExists v; iFrame; iIntros "?"; iApply "F"; iApply "X"; eauto
        | iRight; iDestruct "X" as "[$ X]"; iIntros "Y"; iApply "F"; iApply "X"; eauto ] ].

    (* references *)
    all: try solve [ iIntros "F #C X";
                     iDestruct "X" as (v) "[? X]"; iExists v; iFrame; iIntros "?"; iApply "F"; iApply "X"; eauto ].

    { (* arrays *)
      iIntros "F #C"; iApply (fold_left_frame with "F"); iModIntro. iIntros (???) "F"; iApply "C"; eauto.
    }

    { (* aggregates *)
      case_match; last by iIntros "X C"; iApply "C"; eauto.
      case_match; try by iIntros "X C"; iApply "C"; eauto.
      { (* unions *)
        iIntros "F #C X"; iDestruct "X" as (?) "X".
        iExists _; iDestruct "X" as "[$ X]".
        iIntros "Y"; iSpecialize ("X" with "Y").
        case_match; last by iApply "F".
        case_match; eauto.
        case_match; first by iApply "F".
        iRevert "X"; iApply "C"; eauto. }
      { (* struct *)
        iIntros "F #C".
        iApply (fold_left_frame with "[F]").
        { iApply (fold_left_frame with "[F]").
          { iIntros "[$ X] Y"; iApply "F"; iApply "X"; eauto. }
          { iModIntro.
            iIntros (???) "F". case_match; eauto.
            iApply "C"; eauto. } }
        { iModIntro.
          iIntros (???) "F". case_match; eauto.
          iApply "C"; eauto. } } }
  Qed.

        { iModIntro.
          iIntros (???) "F". case_match; eauto.
  Qed.

End defs.

Notation wp_make_const tu := (cv_cast tu (CV.m 1) (CV.c 1)).
Notation wp_make_mutable tu := (cv_cast tu (CV.c 1) (CV.m 1)).
