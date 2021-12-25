(*
 * Copyright (C) BedRock Systems Inc. 2021-2022
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.word.base.

#[local] Set Primitive Projections.
#[local] Set Printing Coercions.
#[local] Open Scope Z_scope.

Module Type WORD_TYPE.
  Parameter Inline W : wordT.
End WORD_TYPE.

Module Type WORD_MODULUS (Import WT : WORD_TYPE).
  Parameter Inline m : Z.
  Axiom m_spec : m = word.modulus W.
End WORD_MODULUS.

Module Type WORD_MIN_SIGNED  (Import WT : WORD_TYPE).
  Parameter Inline ms : Z.
  Axiom ms_spec : ms = - word.half_modulus W.
End WORD_MIN_SIGNED.
