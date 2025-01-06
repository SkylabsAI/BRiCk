(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.NArith.NArith.

Section with_F.
  Variable T : Type.

  Fixpoint pow (F : Type -> Type) (p : positive) : Type :=
    match p with
    | xH => F T
    | xI p => F (pow (fun x => F (F x)) p)
    | xO p => pow (fun x => F (F x)) p
    end.

  Fixpoint gather (F : Type -> Type)
    (interp : forall {U}, (T -> U) -> T -> F U)
    (p : positive) : T -> pow F p :=
     match p as p return T -> pow F p with
     | xO p => gather (fun x : Type => F (F x)) (fun (U : Type) (k : T -> U) => interp (interp k)) p
     | xI p => interp (gather (fun x : Type => F (F x)) (fun (U : Type) (k : T -> U) => interp (interp k)) p)
     | xH => interp id
     end.

End with_F.

(* NOTE: this reverses the order of the list. *)
Definition list_for T p := gather (list T) (fun x => T -> x) (fun _ K xs x => K (cons x xs)) p nil.
