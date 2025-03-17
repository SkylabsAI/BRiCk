(*
 * Copyright (c) 2020 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** NOTE FOR MAINTAINTERS: This is the central authority for controlling the
  right own instances to use. *)

Require Export bedrock.lang.si_logic.bi. (** <- exporting [siProp] *)
Require Export iris.base_logic.lib.own. (* <- exporting [inG] and [gFunctors] *)
Require Export bedrock.lang.bi.own. (* <- general [own]. *)

(** Own instances for iProp, currently not exported **)
(* Require Export bedrock.lang.base_logic.iprop_own. *)

(** Own instances for monPred, currently exported. **)
Require Export bedrock.lang.base_logic.monpred_own.
