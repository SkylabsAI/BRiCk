(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Strings.Byte.
Require Coq.Strings.String.
Require Import Coq.Lists.List.
Require Coq.Numbers.BinNums.
Require Import Coq.Array.PArray.
Require Import Coq.Numbers.Cyclic.Int63.Uint63.

(* Encoding of strings using packed bits
 * the first word is the length
 * NOTE because we only have 63 bits available,
 * we only store 7 bytes rather than 8
 *)
Set Primitive Projections.
Record ident : Set := Ident { ident_bytes : array Uint63.int }.

Definition bit (n : Uint63.int) (b : bool) : Uint63.int :=
  if b
  then Uint63.lsl 1%int63 n
  else 0%int63.

Section with_notation.
  Import BinNums String Ascii.
  #[local] Infix "b|" := Uint63.lor (at level 30).
  Fixpoint nat_to_int (n : nat) (acc : Uint63.int) : Uint63.int :=
    match n with
    | 0 => acc
    | S n => nat_to_int n (Uint63.add acc 1)
    end.

  Fixpoint pos_to_int (p : positive) (acc : Uint63.int) : Uint63.int :=
    match p with
    | xH => acc
    | xI p => pos_to_int p ((Uint63.lsl acc 1) b| 1)
    | xO p => pos_to_int p (Uint63.lsl acc 1)
    end.

  Search byte N.
  Definition to_int (a : Byte.byte) : Uint63.int :=
    of_Z (BinIntDef.Z.of_N (to_N a)).

  #[local]
  Definition int_to_nat (i : int) : nat := BinIntDef.Z.to_nat (to_Z i).
  #[local]
  Definition int_to_byte (i : int) : Byte.byte :=
    match of_N (BinIntDef.Z.to_N (to_Z i)) with
    | None => x00
    | Some x => x
    end.

End with_notation.

#[local]
Fixpoint next_string (acc : Uint63.int) (n : nat) (s : list Byte.byte) : Uint63.int * list Byte.byte :=
  match n , s with
  | S n , List.cons b s =>
    next_string (Uint63.add (Uint63.lsl acc 8%int63) (to_int b)) n s
  | _ , nil => (acc, s)
  | 0%nat , s => (acc, s)
  end.

Definition parse_ident (s : list Byte.byte) : ident :=
  let n := List.length s in
  let len := nat_to_int n 0 in
  let empty := make (((6+7) + len) / 7)%uint63 0%uint63 in
  let arr := set empty 0 len in
  Ident ((fix populate from n s arr :=
     match s with
     | nil => arr
     | s => let (v,s) := next_string 0 7 s in
           match n with
           | 0 => arr
           | S n => populate (1 + from)%uint63 n s (set arr from v)
           end
     end) 1%int63 n s arr).

Definition print_ident (s : ident) : list Byte.byte :=
  let s := s.(ident_bytes) in
  let len := get s 0%uint63 in
  let len_nat := int_to_nat len in
  let int_min a b := if leb a b then a else b in
  let shift (len : int) : int := (8 * (int_min len 7 - 1))%uint63 in
  (fix go rest (resti : int) i (r : int) byte :=
     match rest with
     | 0 => nil
     | S rest =>
       let resti := (resti - 1)%uint63 in
       let a := int_to_byte (Uint63.land (Uint63.lsr byte r) 255) in
       let '(nexti, nextr, byte) :=
         if is_zero r
         then (* go to the next byte *)
           (i + 1, shift resti, get s i)
         else (* shift 8 fewer bits in this byte *)
           (i, r - 8, byte)
       in
       a :: go rest resti nexti nextr byte
     end)%uint63 len_nat len 2%uint63 (shift len) (get s 1).

Declare Scope ident_scope.
Delimit Scope ident_scope with ident.
String Notation ident parse_ident print_ident : ident_scope.

Module Type TEST.
  Import Coq.Strings.String.
  Definition sanity (s : string) :=
    if String.eqb (string_of_list_byte (print_ident (parse_ident (list_byte_of_string s)))) s then True else False.

  Succeed Example _1 : sanity "a" := I.
  Succeed Example _1 : sanity "ab" := I.
  Succeed Example _1 : sanity "abc" := I.
  Succeed Example _1 : sanity "abcd" := I.
  Succeed Example _1 : sanity "abcde" := I.
  Succeed Example _1 : sanity "abcdef" := I.
  Succeed Example _1 : sanity "abcdefg" := I.
  Succeed Example _1 : sanity "abcdefgh" := I.
  Succeed Example _1 : sanity "abcdefghi" := I.
  Succeed Example _1 : sanity "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf" := I.
End TEST.
