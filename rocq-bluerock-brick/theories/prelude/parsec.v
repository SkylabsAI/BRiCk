(*
 * Copyright (C) BedRock Systems Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.prelude.
Require Import bedrock.prelude.bytestring.

Require Export bedrock.upoly.upoly.
Require Export bedrock.upoly.parsec.

#[local] Set Universe Polymorphism.
#[local] Unset Universe Minimization ToSet.

Require Import bedrock.prelude.pstring.
Require Import Stdlib.Strings.PrimString.
Require Import Stdlib.Numbers.Cyclic.Int63.PrimInt63.
Require Import Stdlib.Numbers.Cyclic.Int63.Uint63.

Import UPoly.

Section char_parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.

  Notation stream := (PrimString.string * PrimInt63.int)%type.
  Notation tok := PrimString.char63.

  Notation M := (M stream F).

  Instance next_list_byte : Next stream tok := {|
    next '(s, i) :=
      if PrimInt63.ltb i (PrimString.length s) then
        Some (PrimString.get s i, (s, PrimInt63.add i 1))
      else
        None
  |}.

  Definition run_bs {T} (p : M T) (b : PrimString.string) : F (option (stream * T)) :=
    fmap (M:=eta option) (fun '(a,b) => (a, b)) <$> run p (b, 0%uint63).

  Definition run_full_bs {T} (p : M T) (b : PrimString.string) : F (option T) :=
    run_full p (b, 0%uint63).

  Definition digit : M tok :=
    char (fun c => andb (PrimInt63.leb ("0"%char63 : char63) c) (PrimInt63.leb c ("9"%char63 : char63))).

  Definition exact_bs (b : list tok) : M unit :=
    exact b.

  Definition exact_char (b : tok) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => bool_decide (b = b')).

  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ascii_of_char63 (c : char63) : Ascii.ascii :=
    Ascii.ascii_of_N (Z.to_N (Uint63.to_Z c)).

  Definition ws : M unit :=
    const () <$> (star $ char (fun c => strings.Ascii.is_space $ ascii_of_char63 c)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  (* A note about effects:
     [not p] will roll-back monadic changes of parsec, but will *not* roll back
     monadic changes in [F]. Therefore, users should be careful about [F] effects
     in [p]. Generally, [p] should be effect free in [F].
   *)
End char_parsec.

(*

Section char_parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.
  Notation M := (M bs F).

  Instance next_list_byte : Next bs Byte.byte.
  Proof. constructor. destruct 1. exact None. apply Some. done. Qed.

  Definition run_bs {T} (p : M T) (b : bs) : F (option (bs * T)) :=
    fmap (M:=eta option) (fun '(a,b) => (a, b)) <$> run p b.

  Definition run_full_bs {T} (p : M T) (b : bs) : F (option T) :=
    run_full p b.

  Definition digit : M Byte.byte :=
    char (fun x => bool_decide (Byte.to_N "0" ≤ Byte.to_N x ≤ Byte.to_N "9")%N).

  Definition exact_bs (b : bs) : M unit :=
    exact $ BS.print b.

  Definition exact_char (b : Byte.byte) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => bool_decide (b = b')).

  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ws : M unit :=
    const () <$> (star $ char (fun x => strings.Ascii.is_space $ Ascii.ascii_of_byte x)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  (* A note about effects:
     [not p] will roll-back monadic changes of parsec, but will *not* roll back
     monadic changes in [F]. Therefore, users should be careful about [F] effects
     in [p]. Generally, [p] should be effect free in [F].
   *)
End char_parsec.

Section char_parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.
  Notation M := (M (list Byte.byte) F).

  Instance next_list_byte : Next (list Byte.byte) Byte.byte.
  Proof. constructor. destruct 1. exact None. apply Some. done. Qed.

  Definition run_bs {T} (p : M T) (b : bs) : F (option (bs * T)) :=
    fmap (M:=eta option) (fun '(a,b) => (BS.parse a, b)) <$> run p (BS.print b).

  Definition run_full_bs {T} (p : M T) (b : bs) : F (option T) :=
    run_full p (BS.print b).

  Definition digit : M Byte.byte :=
    char (fun x => bool_decide (Byte.to_N "0" ≤ Byte.to_N x ≤ Byte.to_N "9")%N).

  Definition exact_bs (b : bs) : M unit :=
    exact $ BS.print b.

  Definition exact_char (b : Byte.byte) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => bool_decide (b = b')).

  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ws : M unit :=
    const () <$> (star $ char (fun x => strings.Ascii.is_space $ Ascii.ascii_of_byte x)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  (* A note about effects:
     [not p] will roll-back monadic changes of parsec, but will *not* roll back
     monadic changes in [F]. Therefore, users should be careful about [F] effects
     in [p]. Generally, [p] should be effect free in [F].
   *)
End char_parsec.


Section char_parsec.
  Context {F : Type -> Type} {MR : MRet F} {FM : FMap F} {MB : MBind F}.

  Notation stream := (PrimString.string * PrimInt63.int)%type.
  Notation tok := PrimString.char63.
  Notation M := (M tok F).


  Definition run_bs {T} (p : M T) (b : PrimString.string) : F (option (stream * T)) :=
    fmap (M:=eta option) (fun '(a,b) => (_ a, b)) <$> run p (_ b true).

    fmap (M:=eta option) (fun '(a,b) => _) <$> run p _.

  Definition run_bs {T} (p : M T) (b : bs) : F (option (bs * T)) :=

  Definition run_full_bs {T} (p : M T) (b : bs) : F (option T) :=
    run_full p (BS.print b).

  Definition digit : M Byte.byte :=
    char (fun x => bool_decide (Byte.to_N "0" ≤ Byte.to_N x ≤ Byte.to_N "9")%N).

  Definition exact_bs (b : bs) : M unit :=
    exact $ BS.print b.

  Definition exact_char (b : Byte.byte) : M unit :=
    fmap (fun _ => ()) $ char (fun b' => bool_decide (b = b')).

  Definition quoted {U V T} (pre : M U) (post : M V) (p : M T) : M T :=
    (fun _ x _ => x) <$> pre <*> p <*> post.

  Definition ws : M unit :=
    const () <$> (star $ char (fun x => strings.Ascii.is_space $ Ascii.ascii_of_byte x)).

  Definition ignore_ws {T} (p : M T) : M T :=
    quoted ws ws p.

  (* A note about effects:
     [not p] will roll-back monadic changes of parsec, but will *not* roll back
     monadic changes in [F]. Therefore, users should be careful about [F] effects
     in [p]. Generally, [p] should be effect free in [F].
   *)
End char_parsec.

*)
