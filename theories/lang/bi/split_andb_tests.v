(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bedrock.lang.bi.split_andb.

Section test.
  #[local] Ltac go := solve [ unshelve (eexists; apply _) ].

  (** Witnesses matter. *)
  #[local] Arguments ex_intro {_ _} _ {_} : assert.

  Goal exists b, CombineAndB false false b.	Proof. go. Show Proof. Abort.	(* false *)
  Goal exists  b, CombineAndB false true b.	Proof. go. Show Proof. Abort.	(* false *)
  Goal exists b, CombineAndB true false b.	Proof. go. Show Proof. Abort.	(* false *)
  Goal exists b, CombineAndB true true b.	Proof. go. Show Proof. Abort.	(* true *)

  Goal forall b1, exists b, CombineAndB b1 false b.	Proof. go. Show Proof. Abort.	(* false *)
  Goal forall b1, exists b, CombineAndB b1 true b.	Proof. go. Show Proof. Abort.	(* b1 *)

  Goal forall b2, exists b, CombineAndB false b2 b.	Proof. go. Show Proof. Abort.	(* false *)
  Goal forall b2, exists b, CombineAndB true b2 b.	Proof. go. Show Proof. Abort.	(* b2 *)

  Goal forall b, exists bhat, CombineAndB b b bhat.	Proof. go. Show Proof. Abort.	(* b *)
  Goal forall b1 b2, exists b, CombineAndB b1 b2 b.	Proof. go. Show Proof. Abort.	(* b1 && b2 *)
End test.
