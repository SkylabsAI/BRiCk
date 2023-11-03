(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From stdpp Require Import fin_maps.
From bedrock.prelude Require Import base bytestring bs_map.
From bedrock.lang.cpp Require Import syntax.translation_unit syntax.types.

Require Import test.test_translation_unit_validity_cpp.

#[local] Hint Constructors complete_decl complete_basic_type complete_type
  complete_pointee_type wellscoped_type wellscoped_types : core.
#[local] Hint Constructors valid_decl : core.
#[local] Hint Extern 10 => done : core.

#[local] Hint Extern 10 => match goal with
| H : In _ _ |- _ => simpl in *; intuition simplify_eq
end : core.

Goal complete_translation_unit module.(types) module.(symbols).
Proof.
  rewrite /complete_translation_unit /complete_type_table /complete_symbol_table.
  (* split; (unshelve eapply map_Forall_to_list; refine _; [shelve..|]). *)
  split.
  all: remember (fun _ _ => _) as P; apply (map_Forall_to_list P); subst.
  all: remember (map_to_list _) as l; lazy in Heql; subst.
  #[local] Opaque module.
  (*all: repeat apply List.Forall_cons; rewrite /type_of_value/=/qual_norm/=; eauto 20.
Qed. *) Admitted.
