(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
(**
   Operator semantics lifted to support casting.
 *)
Require Import bedrock.prelude.numbers.
Require Import iris.proofmode.tactics.

From bedrock.lang.bi Require Import only_provable.
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import mpred operator.
Require Import bedrock.lang.bi.errors.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv} (tu : translation_unit).

  (** Integral Promotion -- fused static and dynamic semantics
   *)
  #[local]
  Definition to_integral (ty : type) (v : val) (Q : type -> val -> mpred) : mpred :=
    match promote_integral tu ty with
    | Some ity =>
        ∃ v', [| conv_int tu ty ity v v' |] ∗ Q ity v'
    | _ => False
    end%I.

  (** [cast_op] is the lifted form of [eval_binop] which additional performs promotions.
      For example, [cast_op tu b Tchar Tshort Tint (Vint 1) (Vint 1) (Vint 2)] holds
      because the [Tchar] and [Tshort] are promoted to [Tint] and the addition occurs.

      NOTE: In accordance with C++ semantics, the return type is a function of the inputs
            (see [convert_type_op])

      TODO: This definition could use [convert_type_op] directly which would simplify it.
            The only benefit of this definition is that it seems like it is slightly closer
            to the standard text which states says "after the usual integral promotions",
            implying that each operand is promoted to an integral type before being converted
            to the computation type.
    *)
  Definition cast_op (b : BinOp) (ty1 ty2 : type) (resultT : type) (v1 v2 : val) : val -> mpred :=
    if is_pointer ty1 && is_pointer ty2 then
      (* pointer-pointer operations *)
      eval_binop tu b ty1 ty2 resultT v1 v2
    else if is_pointer ty1 && is_arithmetic ty2 then
      (* pointer-integer operations *)
      fun v_result =>
        to_integral ty2 v2 (fun ity2 iv2 =>
          eval_binop tu b ty1 ity2 resultT v1 iv2 v_result)
    else if is_arithmetic ty1 && is_pointer ty2 then
      (* integer-pointer operations *)
      fun v_result =>
        to_integral ty1 v1 (fun ity1 iv1 =>
          eval_binop tu b ity1 ty2 resultT iv1 v2 v_result)
    else if is_arithmetic ty1 && is_arithmetic ty2 then
      (* integer-integer operations *)
      fun v_result =>
      to_integral ty1 v1 (fun ity1 iv1 =>
      to_integral ty2 v2 (fun ity2 iv2 =>
        match b with
        | Bshl | Bshr =>
          (* heterogeneous operators *)
          eval_binop tu b ity1 ity2 resultT iv1 iv2 v_result
        | Badd | Bsub | Bmul | Bdiv | Bmod
        | Band | Bor | Bxor
        | Beq | Bneq
        | Blt | Ble | Bgt | Bge
        | Bcmp =>
          (* homogeneous operators *)
          match promote_arith ity1 ity2 with
          | Some to =>
            ∃ tv1 tv2, [| conv_int tu ity1 to iv1 tv1 |] ∗
                      [| conv_int tu ity2 to iv2 tv2 |] ∗
                      eval_binop tu b to to resultT tv1 tv2 v_result
          | _ => False
          end
        | Bdotp => False
        | Bdotip => False
        end%I))
    else fun _ => UNSUPPORTED "cast-op".

  Definition cast_op_alt b ty1 ty2 rty v1 v2 rv :
    match convert_type_op tu b ty1 ty2 with
    | Some (tl, tr, rty') =>
        [| rty = rty' |] ∗
        ∃ v1' v2', [| convert tu ty1 tl v1 v1' |] ∗
                  [| convert tu ty2 tr v2 v2' |] ∗
                  eval_binop tu b tl tr rty v1' v2' rv
    | _ => False
    end
    ⊢ cast_op b ty1 ty2 rty v1 v2 rv.
  Proof.
    rewrite /convert_type_op/cast_op.
    destruct (is_pointer ty1) eqn:?; simpl; try rewrite andb_false_r.
    { destruct (is_pointer ty2) eqn:?; simpl; try rewrite andb_false_r.
      { destruct b; try iIntros "[]".
        rewrite /convert. rewrite Heqb0 Heqb1/=.
        iIntros "X"; iDestruct "X" as (? ?) "(% & % & % & X)"; subst; eauto.
      }
      {           rewrite (is_pointer_not_arithmetic _ Heqb0); simpl.
        destruct (is_arithmetic ty2) eqn:?; simpl; try solve [ iIntros "[]" ].
        rewrite /to_integral.
        destruct b; try solve [ iIntros "[]" ];
          destruct (promote_integral tu ty2) eqn:?; eauto.
        - rewrite /convert. rewrite Heqb0 Heqb1 Heqb2/=.
          iIntros "X"; iDestruct "X" as (??) "(% & % & % & X)"; subst.
          case_match; try contradiction.
          iExists _; iFrame. eauto.
        - rewrite /convert. rewrite Heqb0 Heqb1 Heqb2/=.
          iIntros "X"; iDestruct "X" as (??) "(% & % & % & X)"; subst.
          case_match; try contradiction.
          iExists _; iFrame. eauto. } }
    { (* is_pointer ty1 = false *)
      destruct (is_arithmetic ty1) eqn:?; simpl; try rewrite andb_false_r; try iIntros "[]".
      { destruct (is_pointer ty2) eqn:?; simpl; try rewrite andb_false_r; try iIntros "[]".
        { destruct b; try solve [ iIntros "[]" ];
            rewrite /to_integral;
            destruct (promote_integral tu ty1) eqn:?; eauto;
            rewrite /convert Heqb0 Heqb1 Heqb2/=;
              iIntros "X"; iDestruct "X" as (??) "(% & % & % & X)"; subst;
            case_match; try contradiction;
            iExists _; iFrame; eauto. }
        { destruct (is_arithmetic ty2) eqn:?; simpl; try iIntros "[]".
          { rewrite /to_integral.
            destruct (promote_integral tu ty1) eqn:?; eauto.
            destruct (promote_integral tu ty2) eqn:?; eauto.
            case_match; try solve [ iIntros "[]" ].
            destruct p as [[??]?].
            iIntros "X".
            rewrite /convert. rewrite Heqb0 Heqb1 Heqb2 Heqb3/=.
            iDestruct "X" as (v1' v2') "(%C1 & %C2 & % & X)"; subst.
            destruct (is_arithmetic t1) eqn:?; try contradiction.
            destruct (is_arithmetic t2) eqn:?; try contradiction.
            (* this relies on:
                1. integral promotions are lossless
                2. [conv_int] is transitive when the first one is lossless.
              *)
            admit. } } } }
  Admitted.
End with_cpp.
