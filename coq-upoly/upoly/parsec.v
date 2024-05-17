(*
 * Copyright (C) BedRock Systems Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Strings.Byte.
Require Import stdpp.base.
Require Import stdpp.decidable.
Require Import stdpp.strings.
Require Import bedrock.upoly.upoly.
Require Import bedrock.upoly.optionT.
Require Import bedrock.upoly.stateT.

(** ** parsec
    Simple implementation of a parser combinator library.

    NOTE: [M] is a monad transformer so additional state can be
          threaded through the parsing.
 *)

Import UPoly.
Section parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.

  #[local] Notation bs := (list Byte.byte).

  Definition M (T : Type) : Type :=
    stateT.M bs (optionT.M F) T.

  Definition run {T} (m : M T) : bs -> F _ :=
    fun str => optionT.run (stateT.run m str).

  #[global] Instance MRet_M : MRet M := @stateT.ret _ _ _.
  #[global] Instance FMap_M : FMap M := @stateT.map _ _ _.
  #[global] Instance MBind_M : MBind M := @stateT.bind _ _ _.
  #[global] Instance Ap_M : Ap M := _.
  #[global] Instance MFail_M : MFail M := @stateT.fail _ _ _.
  #[global] Instance MLift_M : MLift F M := fun _ m => lift (optionT.lift m).
  #[global] Instance M_Alternative : Alternative M :=
    fun _ pl pr =>
      stateT.mk $ fun s => alternative (stateT.runp pl s) (fun tt => stateT.runp (pr tt) s).

  #[global] Hint Opaque M : typeclass_instances.
  #[local] Open Scope monad_scope.

  Definition any : M Byte.byte :=
    let* l := stateT.get in
    match l with
    | nil => mfail
    | b :: bs => const b <$> stateT.put bs
    end.

  (* end-of-stream *)
  Definition eos : M unit :=
    let* l := stateT.get in
    match l with
    | nil => mret tt
    | _ => mfail
    end.

  Definition char (P : Byte.byte -> bool) : M Byte.byte :=
    let* c := any in
    if P c then mret c else mfail.

  Definition epsilon : M unit := mret tt.

  Definition or {T} (pl pr : M T) : M T :=
    pl <|> pr.

  Fixpoint anyOf {T} (ls : list (M T)) : M T :=
    match ls with
    | nil => mfail
    | l :: ls => l <|> anyOf ls
    end.

  (* NOTE: this is basically [sequence]/[transpose] *)
  Definition seqs {T} (ls : list (M T)) : M (list T) :=
    sequence ls.

  Definition optional {T} (p : M T) : M (option T) :=
    (Some <$> p) <|> mret None.

  Fixpoint star_ (fuel : nat) {T} (p : M T) : M (list T) :=
    let* x := optional p in
    match x with
    | None => mret nil
    | Some v =>
        match fuel with
        | 0 => mfail (* This is usually the programmers fault *)
        | S fuel => cons v <$> star_ fuel p
        end
    end.

  Definition star : forall {T}, _ := @star_ 1000.

  Definition plus {T} (p : M T) : M (list T) :=
    cons <$> p <*> star p.

  Definition peek : M (option Byte.byte) :=
    let k l :=
      match l with
      | nil => None
      | x :: _ => Some x
      end
    in
    k <$> stateT.get.

  Definition sepBy {T} (sep : M unit) (p : M T) : M (list T) :=
    (cons <$> p <*> (star ((fun _ x => x) <$> sep <*> p))) <|> mret nil.


  Fixpoint exact_ (b : bs) (input : bs) {struct b} : optionT.M F (UTypes.prod bs unit) :=
    match b with
    | nil => mret (UTypes.pair input tt)
    | x :: xs =>
        match input with
        | y :: ys =>
            if Byte.eqb x y then
              exact_ xs ys
            else mfail
        | nil => mfail
        end
    end.

  Definition exact (b : bs) : M unit :=
    stateT.mk $ exact_ b.

  Definition digit : M Byte.byte :=
    char (fun x => BinNatDef.N.leb (Byte.to_N "0") (Byte.to_N x) &&
                BinNatDef.N.leb (Byte.to_N x) (Byte.to_N "9")).

  Definition exact_char (b : Byte.byte) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => Byte.eqb b b').

  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ws : M unit :=
    const () <$> (star $ char (fun x => strings.is_space $ Ascii.ascii_of_byte x)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  Definition not_char (P : Byte.byte -> bool) : M unit :=
    let* x := parsec.peek in
    match x with
    | None => mret ()
    | Some x => if P x then mfail else mret ()
    end.

End parsec.
Arguments M _ _ : clear implicits.
