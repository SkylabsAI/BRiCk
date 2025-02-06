(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Structures.OrderedTypeAlt.
Require Import Stdlib.FSets.FMapAVL.
Require Import bedrock.prelude.avl.
Require Import bedrock.prelude.array_map.
Require Import bedrock.prelude.compare.
Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.compare.

(** ** Name maps *)

#[global] Declare Instance name_comparison {lang} :
  Comparison (compareN (lang:=lang)).	(** TODO *)

Module Import internal.

  Module Type LANG.
    Parameter Inline lang : lang.t.
  End LANG.

  Module NameMap (Lang : LANG).
    Module Compare.
      Definition t : Type := name' Lang.lang.
      #[local] Definition compare : t -> t -> comparison := compareN.
      #[local] Infix "?=" := compare.
      #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
      Proof. exact: compare_antisym. Qed.
      #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
      Proof. exact: base.compare_trans. Qed.
    End Compare.
    Definition key := name' Lang.lang.
    Definition inh : Inhabited key := _.
    Definition compare := Compare.compare.

    Module AVL.
      Module Key := OrderedType_from_Alt Compare.
      Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
      Proof. apply name_leibniz_comparison. Qed.

      Include FMapAVL.Make Key.
      Include FMapExtra.MIXIN Key.
      Include FMapExtra.MIXIN_LEIBNIZ Key.
    End AVL.

    Include array_map.map.
    #[global] Instance t_lookup {A} : Lookup key A (t A) :=
      fun k (m : t A) => find k m.

    #[global] Instance t_empty `{inh : Inhabited A} : Empty (t A) :=
      @empty _ _.

  End NameMap.

End internal.

Module NM.
  #[local] Definition lang := lang.cpp.
  Include NameMap.

  #[global] Arguments NM.t_lookup _ !_ !_.
  #[global] Arguments NM.find _ !_ !_.
  #[global] Arguments NM.find_key _ !_ !_.
  #[global] Arguments array_map.Uint63_Fast.to_Z_pos !_.
  #[global] Arguments array_map.Uint63_Fast.to_pos_rec !_ !_ !_.
  #[global] Arguments NM.binary_search !_ !_ !_.
  #[global] Arguments NM.bisect_N !_.
  #[global] Arguments NM.bisect_pos !_ !_.
End NM.

Module TM.
  #[local] Definition lang := lang.temp.
  Include NameMap.
End TM.
