Require Import NArith.

Section with_F.
  Context {T : Type}.

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

Definition list_for T p := @gather (list T) (fun x => T -> x) (fun _ K xs x => K (cons x xs)) p nil.

Definition map_for K V p := @gather (list (K * V)) (fun x => K -> V -> x) (fun _ K xs k v => K (cons (k,v) xs)) p nil.
