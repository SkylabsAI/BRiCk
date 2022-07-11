Import Coq.Init.Byte(byte).
From Coq.Numbers Require HexadecimalString HexadecimalFacts.
From stdpp Require Import strings.
From bedrock.prelude Require Import base bytestring.

#[local] Open Scope N_scope.
#[local] Open Scope bs.

Definition printable (x : byte) := 32 <= Byte.to_N x < 128.

Fixpoint take_while {A} P `{∀ x, Decision (P x)} (xs : list A) : (list A * list A) :=
  match xs with
  | [] => ([], [])
  | x :: xs =>
    if decide (P x) then
      let (xs', ys') := take_while P xs in
      (x :: xs', ys')
    else
      ([], x :: xs)
    end.

Fixpoint take_while_acc {A} P `{∀ x, Decision (P x)} (acc xs : list A) : (list A * list A) :=
  match xs with
  | [] => (rev acc, [])
  | x :: xs =>
    if decide (P x) then
      take_while_acc P (x :: acc) xs
    else
      (rev acc, x :: xs)
    end.

Definition take_while' {A} P `{∀ x, Decision (P x)} (xs : list A) : (list A * list A) :=
  take_while_acc P [] xs.

Definition pad_byte (x : Hexadecimal.uint) : Hexadecimal.uint :=
  let xs := HexadecimalFacts.to_list x in
  HexadecimalFacts.of_list (replicate (2 - length xs) HexadecimalFacts.d0 ++ xs).

Definition byte_to_num_bs (x : byte) : bs :=
  BS.of_string $ HexadecimalString.NilEmpty.string_of_uint $ pad_byte $
    N.to_hex_uint $ Byte.to_N x.

Definition escape_byte (x : byte) : bs :=
  "Byte.x" ++ byte_to_num_bs x.

Definition guard_empty {A} (xs : list A) (rest : bs) : bs :=
  if bool_decide (xs = []) then "" else rest.

Definition escape_bytes (xs : list byte) : bs :=
  guard_empty xs
    (foldr (λ x xs, "(BS.String Byte.x" ++ byte_to_num_bs x ++ " " ++ xs ++ ")") """""" xs).

(* TODO: escape double quotes in strings. *)
Definition noescape_bytes (xs : list byte) : bs :=
  guard_empty xs ("""" ++ BS.parse xs ++ """").

Definition join_nonempty (xs ys : bs) : bs :=
  if bool_decide (xs <> "" ∧ ys <> "") then
    xs ++ " ++ " ++ ys
  else
    xs ++ ys.

(* Notation bs_empty str := (bool_decide (str = "")%bs).
Notation bs_nonempty str := (bool_decide (str <> "")%bs). *)
Fixpoint pretty_bytes_go (n : nat) (xs : list byte) : bs :=
  match n with
  | 0%nat => ""
  | S n' =>
    let (pfx, mid) := take_while' printable xs in
    let (esc, sfx) := take_while' (λ x, ¬ printable x) mid in
    join_nonempty (noescape_bytes pfx) (escape_bytes esc) ++ guard_empty sfx
      (* Either [pfx] or [esc] was nonempty, so we output [" ++ "]
      unconditionally. *)
      (" ++ " ++ pretty_bytes_go n' sfx)
  end.

Definition pretty_bytes (str : bs) : bs :=
 pretty_bytes_go (S (BS.length str)) (BS.print str).

Section test.
(* Eval cbv in (BS.String Byte.x45 (BS.String Byte.x4e (BS.String Byte.x4f (BS.String
  Byte.x4e (BS.String Byte.x45 BS.EmptyString))))). *)
  Let str :=
    (BS.String Byte.x0d (BS.String Byte.x0a (BS.String Byte.x57 (BS.String Byte.x65
    (BS.String Byte.x6c (BS.String Byte.x63 (BS.String Byte.x6f (BS.String Byte.x6d
    (BS.String Byte.x65 (BS.String Byte.x20 (BS.String Byte.x74 (BS.String Byte.x6f
    (BS.String Byte.x20 (BS.String Byte.x74 (BS.String Byte.x68 (BS.String Byte.x65
    (BS.String Byte.x20 (BS.String Byte.x42 (BS.String Byte.x48 (BS.String Byte.x56
    (BS.String Byte.xe2 (BS.String Byte.x84 (BS.String Byte.xa2 (BS.String Byte.x20
    (BS.String Byte.x55 (BS.String Byte.x41 (BS.String Byte.x52 (BS.String Byte.x54
    (BS.String Byte.x20 (BS.String Byte.x6d (BS.String Byte.x75 (BS.String Byte.x6c
    (BS.String Byte.x74 (BS.String Byte.x69 (BS.String Byte.x70 (BS.String Byte.x6c
    (BS.String Byte.x65 (BS.String Byte.x78 (BS.String Byte.x65 (BS.String Byte.x72
    (BS.String Byte.x20 (BS.String Byte.x63 (BS.String Byte.x6f (BS.String Byte.x6e
    (BS.String Byte.x73 (BS.String Byte.x6f (BS.String Byte.x6c (BS.String Byte.x65
    BS.EmptyString)))))))))))))))))))))))))))))))))))))))))))))))).

  (* Search list prod Prop outside EnvRing Ring_polynom Tauto OrderedRing Field_theory RingMicromega SetoidList micromega.Refl. *)
  (* Eval cbv in (BS.print str)%byte. *)
  (* Search list Prop "take".
  Search list Prop "While". *)

  (* Eval cbv in str. *)
  (* Eval cbv in
    let (a, b) := take_while printable (BS.print str) in
    (BS.parse a, BS.parse b).
  Eval cbv in
    let (a, b) := take_while' printable (BS.print str) in
    (BS.parse a, BS.parse b).
  Eval cbv in *)
  Goal take_while printable (BS.print str) = take_while' printable (BS.print str).
  Proof. done. Qed.

(* Eval cbv in N.to_hex_uint $ Byte.to_N Byte.x0d. *)

  Goal escape_byte Byte.x00 = "Byte.x00". done. Abort.
  Goal escape_byte Byte.x0d = "Byte.x0d". done. Abort.
  Goal escape_byte Byte.x1d = "Byte.x1d". done. Abort.
  (* Eval cbv in escape_byte Byte.x0d.
  Eval cbv in escape_byte "A". *)
  Goal escape_byte "A" = "Byte.x41". done. Abort.
  Goal Byte.x41 = "A"%byte. done. Abort.

  Goal (BS.String Byte.x41 (BS.String Byte.x42 (BS.String Byte.x43 ""))) = "ABC".
  Proof. cbv. done. Abort.

  (* Goal True.
  idtac "(BS.String Byte.x41 """")". *)
  Goal escape_bytes (BS.print "A") = "(BS.String Byte.x41 """")".
  Proof. cbv. done. Abort.
(* Eval cbv in escape_bytes (BS.print "ABC"). *)
  Goal escape_bytes (BS.print "ABC") =
    "(BS.String Byte.x41 (BS.String Byte.x42 (BS.String Byte.x43 """")))".
  Proof. cbv. done. Abort.
  Goal escape_bytes [] = "".
  Proof. cbv. done. Abort.

  (* Eval cbv in Byte.to_N <$> BS.print "™". *)
  (* Eval cbv in pretty_bytes "Welcome to the BHV". *)
  Goal pretty_bytes "Welcome to the BHV" = """Welcome to the BHV""".
  (* idtac """Welcome to the BHV"" ++ (BS.String Byte.xe2 (BS.String Byte.x84 (BS.String Byte.xa2 BS.EmptyString)))". *)
  Proof. cbv. done. Abort.
  (* Eval cbv in pretty_bytes "Welcome to the BHV™". *)
  Goal pretty_bytes "Welcome to the BHV™" =
    """Welcome to the BHV"" ++ (BS.String Byte.xe2 (BS.String Byte.x84 (BS.String Byte.xa2 """")))".
  Proof. cbv. done. Abort.


  Goal "Welcome to the BHV™" =
    "Welcome to the BHV" ++ (BS.String Byte.xe2 (BS.String Byte.x84 (BS.String Byte.xa2 BS.EmptyString))).
  Proof. cbv. done. Abort.

  (* Goal True.
idtac
 "(BS.String Byte.x0d (BS.String Byte.x0a """")) ++ ""Welcome to the BHV"" ++ (BS.String Byte.xe2 (BS.String Byte.x84 (BS.String Byte.xa2 """"))) ++ "" UART multiplexer console"""
 .
  Abort. *)

  Goal str =
  (BS.String Byte.x0d (BS.String Byte.x0a "")) ++ "Welcome to the BHV" ++
  (BS.String Byte.xe2 (BS.String Byte.x84 (BS.String Byte.xa2 ""))) ++
  " UART multiplexer console".
  Proof. cbv. done. Abort.

(*
  Eval cbv in pretty_bytes str.
  Eval cbv in "
Welcome to the BHV"%bs ++ "™" ++ " UART multiplexer console"%bs.
Eval cbv in pretty 100 (BS.print str). *)
(* partition *)

End test.
