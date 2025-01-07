(*
 * Copyright (c) 2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Stdlib.NArith.NArith.

Module binary.
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
     | xO p => gather (fun x : Type => F (F x)) (fun U k acc => interp (fun acc => interp k acc) acc) p
     | xI p => interp (gather (fun x : Type => F (F x)) (fun U k acc => interp (fun acc => interp k acc) acc) p)
     | xH => interp id
     end.

End with_F.
End binary.

Module unary.
  Section with_F.
    Variable T : Type.
    Variable F : Type -> Type.

    Fixpoint pow (p : nat) : Type :=
      match p with
      | O => T
      | S p => F (pow p)
      end.

    Context {A} (interp : forall U, (A -> U) -> A -> F U).
    Variable finish : A -> T.
    Fixpoint gather (p : nat) (acc : A) : pow p :=
      match p as p return pow p with
      | O => finish acc
      | S p => interp _ (fun acc => gather p acc) acc
      end.

  End with_F.
End unary.

(* NOTE: this reverses the order of the list. *)
Definition list_for T p : unary.pow (list T) (fun x => T -> x) p :=
  Eval cbv beta iota zeta delta [ unary.gather ] in
    unary.gather (list T) (fun x => T -> x) (fun _ K xs x => K (cons x xs)) (fun x => x) p nil.

Definition combine {T A U} (f : A -> U) (op : T -> A -> A) (acc : A) p : unary.pow U (fun x => T -> x) p :=
  Eval cbv beta iota zeta delta [ unary.gather ] in
    unary.gather U (fun x => T -> x) (fun _ K xs x => K (op x xs)) f p acc.
