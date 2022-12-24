(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.bi.prelude.
Require Import bedrock.lang.cpp.bi.cfractional.
Require Import iris.proofmode.proofmode.
Import ChargeNotation.

#[local] Set Printing Coercions.

Section EXAMPLES.
  Context {PROP : bi}.
  Context (R : CV.t -> PROP) `{!cfractional.CFractional R}.

  Let R_as_fractional q : AsCFractional (R q) R q.
  Proof. exact: Build_AsCFractional. Qed.
  #[local] Existing Instance R_as_fractional.

  (**
  Splitting on [op] is always trivial.
  *)

  Let split_cv_cv cv1 cv2 :
    R (cv1 ⋅ cv2) |-- R cv1 ** R cv2.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_cv_mk cv c q :
    R (cv ⋅ CV.mk c q) |-- R cv ** R (CV.mk c q).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mk_cv cv c q :
    R (CV.mk c q ⋅ cv) |-- R (CV.mk c q) ** R cv.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mk_mk c1 c2 q1 q2 :
    R (CV.mk c1 q1 ⋅ CV.mk c2 q2) |-- R (CV.mk c1 q1) ** R (CV.mk c2 q2).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (**
  Splitting [CV.is_const] knows about [&&].
  *)

  Let split_andb c1 c2 q :
    R (CV.mk (c1 && c2) q) |-- R (CV.mk c1 (q/2)) ** R (CV.mk c2 (q/2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (** Otherwise, both sides get the same [CV.is_const] after the split. *)

  Let split_mut :
    R (CV.mut 1) |-- R (CV.mut (1/2)) ** R (CV.mut (1/2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_const :
    R (CV.const 1) |-- R (CV.const (1/2)) ** R (CV.const (1/2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mk c :
    R (CV.mk c 1) |-- let Rhalf := R (CV.mk c (1/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_cv cv :
    R cv |-- let Rhalf := R (CV.mk (CV.is_const cv) (CV.frac cv/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (*
  Splitting fractions knows about a few constants and (some factors
  of) [q1 + q2].
  *)

  Let split_½ : R (CV.mut (1/2)) |-- let Rhalf := R (CV.mut (1/4)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_1 : R (CV.mut 1) |-- let Rhalf := R (CV.mut (1/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_q q : R (CV.mut q) |-- let Rhalf := R (CV.mut (q/2)) in Rhalf ** Rhalf.
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  Let split_sum q1 q2 : R (CV.mut (q1 + q2)) |-- R (CV.mut q1) ** R (CV.mut q2).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  Let split_mul_l p q1 q2 :
    R (CV.mut (p * (q1 + q2))) |-- R (CV.mut (p * q1)) ** R (CV.mut (p * q2)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.
  Let split_mul_r p q1 q2 :
    R (CV.mut ((q1 + q2) * p)) |-- R (CV.mut (q1 * p)) ** R (CV.mut (q2 * p)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  Let split_div p q1 q2 :
    R (CV.mut ((q1 + q2) / p)) |-- R (CV.mut (q1 / p)) ** R (CV.mut (q2 / p)).
  Proof. iIntros "[R1 R2]". by iFrame "R1 R2". Abort.

  (**
  Combining two variables produces [op].
  *)
  Let combine_cv cv :
    R cv ** R cv |-- R (cv ⋅ cv).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_cv_cv cv1 cv2 :
    R cv1 ** R cv2 |-- R (cv1 ⋅ cv2).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (**
  Combining anything other than two variables expands [op] and
  attempts to simplify the [CV.is_const] part and the [CV.is_frac]
  part. (This example does not simplify.)
  *)

  Let combine_cv_mk cv c :
    R cv ** R (CV.mk c (1/2)) |-- R (CV.mk (CV.is_const cv && c) (CV.frac cv + 1/2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_cv cv c :
    R (CV.mk c (1/2)) ** R cv|-- R (CV.mk (c && CV.is_const cv) (1/2 + CV.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (** Simplifing [CV.is_const] given two concrete values *)

  Let combine_mut_mut :
    R (CV.mut (1/2)) ** R (CV.mut (1/2)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mut_const :
    R (CV.mut (1/2)) ** R (CV.const (1/2)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_const_mut :
    R (CV.const (1/2)) ** R (CV.mut (1/2)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_const_const :
    R (CV.const (1/2)) ** R (CV.const (1/2)) |-- R (CV.const 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (** Simplifing [CV.is_const] given one concrete value *)

  Let combine_mut_var q cv :
    R (CV.mut q) ** R cv |-- R (CV.mut (q + CV.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_var_mut q cv :
    R cv ** R (CV.mut q) |-- R (CV.mut (CV.frac cv + q)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_const_var q cv :
    R (CV.const q) ** R cv |-- R (CV.mk (CV.is_const cv) (q + CV.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_var_const q cv :
    R cv ** R (CV.const q) |-- R (CV.mk (CV.is_const cv) (CV.frac cv + q)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mut_mk c :
    R (CV.mut (1/2)) ** R (CV.mk c (1/2)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_mut c :
    R (CV.mk c (1/2)) ** R (CV.mut (1/2)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_const_mk c :
    R (CV.const (1/2)) ** R (CV.mk c (1/2)) |-- R (CV.mk c 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_const c :
    R (CV.mk c (1/2)) ** R (CV.const (1/2)) |-- R (CV.mk c 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (** Simplifying [CV.is_const] given no concrete values *)

  Let combine_cv cv :
    let Rhalf := R (CV.mk (CV.is_const cv) (CV.frac cv/2)) in Rhalf ** Rhalf |-- R cv.
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mk c :
    let Rhalf := R (CV.mk c (1/2)) in Rhalf ** Rhalf |-- R (CV.mk c 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_cv_mk cv c q :
    R cv ** R (CV.mk c q) |-- R (CV.mk (CV.is_const cv && c) (CV.frac cv + q)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mk_cv cv c q :
    R (CV.mk c q) ** R cv |-- R (CV.mk (c && CV.is_const cv) (q + CV.frac cv)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mk_mk c1 c2 q1 q2 :
    R (CV.mk c1 q1) ** R (CV.mk c2 q2) |-- R (CV.mk (c1 && c2) (q1 + q2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  (**
  Simpifying [CV.frac] is pretty aggressive. We give a few examples.
  *)

  Let combine_quarter q : R (CV.mut (q/4)) ** R (CV.mut (q/4)) |-- R (CV.mut (q/2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_¼ : R (CV.mut (1/4)) ** R (CV.mut (1/4)) |-- R (CV.mut (1/2)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_half q : R (CV.mut (q/2)) ** R (CV.mut (q/2)) |-- R (CV.mut q).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_½ : R (CV.mut (1/2)) ** R (CV.mut (1/2)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine : R (CV.mut (1/4)) ** R (CV.mut (3/4)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine : R (CV.mut (3/4)) ** R (CV.mut (1/4)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine : R (CV.mut (1/3)) ** R (CV.mut (2/3)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine : R (CV.mut (2/3)) ** R (CV.mut (1/3)) |-- R (CV.mut 1).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.

  Let combine_mul_l p q1 q2 :
    R (CV.mut (p * q1)) ** R (CV.mut (p * q2)) |-- R (CV.mut (p * (q1 + q2))).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_mul_r p q1 q2 :
    R (CV.mut (q1 * p)) ** R (CV.mut (q2 * p)) |-- R (CV.mut ((q1 + q2) * p)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
  Let combine_div p q1 q2 :
    R (CV.mut (q1 / p)) ** R (CV.mut (q2 / p)) |-- R (CV.mut ((q1 + q2) / p)).
  Proof. iIntros "[R1 R2]"; iCombine "R1 R2" as "R". by iFrame "R". Abort.
End EXAMPLES.
