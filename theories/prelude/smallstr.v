(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Structures.OrderedType.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.uint63.
Require Import bedrock.prelude.array.
Require Import Coq.Strings.Byte.
Require Coq.Strings.String.
Require Import Coq.Lists.List.
Require Coq.Numbers.BinNums.

Import Uint63 PArray.

#[global] Declare Scope smallstr_scope.
#[global] Delimit Scope smallstr_scope with smallstr.

Module SmallStr.
(* Encoding of strings using packed bits
 * the first word is the length
 * NOTE because we only have 63 bits available,
 * we only store 7 bytes rather than 8
 *)
#[projections(primitive=yes)]
Record t : Set := Smallstr { smallstr_bytes : array Uint63.int }.
#[global] Notation smallstr := t.
#[global] Bind Scope smallstr_scope with t.

#[program]
Definition eq_dec s1 s2 : Decision (s1 = s2) :=
  match PArray.eq_dec s1.(smallstr_bytes) s2.(smallstr_bytes) with
  | left _ => left _
  | right _ => right _
  end.
Next Obligation. intros [] []. simpl. now intros ->. Qed.
Next Obligation. intros [] []. simpl. intros H E. apply H. now injection E. Qed.

Definition eqb (s1 s2 : smallstr) := match eq_dec s1 s2 with left _ => true | _ => false end.

#[global] Instance smallstr_eqdec : EqDecision smallstr := eq_dec.

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

  Definition to_int (a : Byte.byte) : Uint63.int :=
    of_Z (BinIntDef.Z.of_N (to_N a)).

  #[local]
  Definition int_to_nat' (i : int) : nat := BinIntDef.Z.to_nat (to_Z i).

  Definition some_nats_limit := 255%uint63.
  Definition some_nats :=
    Eval vm_compute in
    let a := PArray.make 255 0 in
    let go :=
      fix go n i a :=
        match n with
        | 0 => a
        | S n => go n (i+1)%uint63 (PArray.set a i (int_to_nat' i))
        end
    in
    go (int_to_nat' some_nats_limit) 0%uint63 a.

  Definition int_to_nat i :=
    Eval lazy [some_nats some_nats_limit int_to_nat'] in
    if Uint63.ltb i some_nats_limit then some_nats.[i] else int_to_nat' i.

  #[local]
  Definition int_to_byte' (i : int) : Byte.byte :=
    match of_N (BinIntDef.Z.to_N (to_Z i)) with
    | None => x00
    | Some x => x
    end.

  Definition all_bytes : array byte :=
    Eval vm_compute in
    let a := PArray.make 255 x00 in
    let go :=
      fix go n i a :=
        match n with
        | 0 => a
        | S n => go n (i+1)%uint63 (PArray.set a i (int_to_byte' i))
        end
    in
    go 255 0%uint63 a.

  Definition int_to_byte i := all_bytes.[i].

End with_notation.

Definition to_bits : forall (i : int), list nat :=
  let go := fix go n acc i :=
      match n with
      | 0 => acc
      | S n => go n (int_to_nat (i land 1) :: acc)%uint63 (i >> 1)%uint63
      end
  in
  go 63 [].

Eval lazy in to_bits (255<<48)%uint63.

Definition max_val := Eval cbv in (max_int >> 7)%uint63.
Definition zero_mask sh := ((255 << (sh * 8)) lxor max_val)%uint63.
(* Mask out n many characters from the prefix *)
Definition zero_masks_pref n := (max_val >> (n * 8))%uint63.
Definition zero_masks_suff n := (max_val land (max_val << (n * 8)))%uint63.

Eval lazy in to_bits (zero_masks_pref 6).
Eval lazy in to_bits (zero_masks_suff 6).

Definition len s := let '{|smallstr_bytes := a|} := s in get a 0%uint63.

Definition position (i : Uint63.int) : Uint63.int * Uint63.int :=
  let (q,r) := Uint63.diveucl i 7 in
  (* index 0 is the string length *)
  (q+1, 6-r)%uint63.

Definition div_up (i1 i2 : int) :=
  let (q,r) := diveucl i1 i2 in
  if Uint63.eqb r 0 then q else (q + 1)%uint63.



Fixpoint next_string (acc : Uint63.int) (n : nat) (s : list Byte.byte) : Uint63.int * list Byte.byte :=
  match n , s with
  | S n , List.cons b s =>
    next_string (Uint63.lor (Uint63.lsl acc 8%int63) (to_int b)) n s
  | S _ , _ => (acc << (nat_to_int n 0 * 8), s)%uint63
  | _ , _ => (acc, s)
  end.

Definition fill :=
  Eval lazy [next_string Uint63.add] in
  fix fill n s i arr {struct n} :=
  match s with
  | [] => arr
  | _ =>
      match n with
      | 0 => arr
      | S n =>
          let (v,s) := next_string 0 7 s in
          fill n s (i + 1)%uint63 (set arr i v)
      end
  end.

Definition parse (s : list byte) : smallstr :=
  let len_nat := List.length s in
  let len := nat_to_int len_nat 0 in
  (* 1 uint63 for the string length + ceil(n/7) uint63 for the bytes *)
  let arrlen := (1 + (div_up len 7))%uint63 in
  let arr := PArray.make arrlen 0%uint63 in
  let arr := PArray.set arr 0 len in
  Smallstr (fill len_nat s 1%int63 arr).

Eval lazy in
  let s := parse [x61; x62; x63; x64; x65] in
  s.

Eval lazy in
  parse [x61; x62; x63; x64; x65].


Definition sub_bd (i1 i2 : int) :=
  (if (i2 ≤? i1) then i1 - i2 else 0)%uint63.

Module U.
  (* Underhang information: read __last__ [n] bytes from array index [ind] *)
  Record t := mk
    { n : int;
      ind: int }.
End U.

Module O.
  (* Overhang information: read bytes [k .. k+n] bytes from array index [ind] *)
  Record t := mk
    { k : int;
      n : int;
      ind: int }.
End O.

Module R.
  (* Splitting possibly unaligned reads into underhang, overhang, and aligned reads inbetween, *)
  Record t :=
    mk {
      underhang : option (U.t);
      overhang: option (O.t);
      (* read [n] items starting from array index [ind] and counting downards *)
      ind: int;
      n: int
    }.

  (* [split from len] computes [t]. The following case is the really difficult one:
     - [len < 7]: we treat the entire range as an overhang (which can contain an offset for [from])
   *)
  Definition split from len :=
    let lenlt7 := Uint63.ltb len 7 in
    let under := Uint63.mod from 7 in
    let has_under := Uint63.ltb 0 under in
    let start := div_up from 7 in
    let u := if has_under then  Some {| U.ind := start; U.n := 7-under |}%uint63 else None in
    let e := (from + len)%uint63 in
    let over := Uint63.mod e 7 in
    let has_over := Uint63.ltb 0 over in
    let o_ind := div_up e 7 in

    if has_over && Uint63.ltb len 7 then
      {| underhang := None;
         overhang := Some {|O.ind := o_ind;
                            O.n := if Uint63.ltb over len then over else len;
                            O.k := under
                          |};
         ind := 0;
         n := 0;
      |}%uint63
    else

    let o := if has_over then Some {| O.ind := o_ind; O.n := over; O.k := 0; |} else None in

    let dist := div (len-over-under) 7 in
    let ind := div_up (from+len-over) 7 in
    {| underhang := u;
      overhang := o;
      ind := ind;
      n := dist;
    |}%uint63.
End R.

Fixpoint read_bytes (n : nat) (i : int) (acc : list byte) : list byte :=
  match n with
  | 0 => acc
  | S n =>
      let b := (i land 255)%uint63 in
      let i := (i >> 8)%uint63 in
      read_bytes n i (int_to_byte b :: acc)
  end.

Definition print_sub_aux a from len : list byte :=
Eval cbn beta fix match delta [read_bytes] in
  let r := R.split from len in
  let acc := [] in
  let acc := match r.(R.overhang) with
    | Some o =>
        let bucket := PArray.get a (o.(O.ind)) in
        let bucket := (bucket >> ((7-o.(O.n)-o.(O.k))*8))%uint63 in
        read_bytes (int_to_nat o.(O.n)) bucket acc
    | None => acc
    end
  in
  let go :=
    fix go n pos acc {struct n} :=
      match n with
      | 0 => acc
      | S n =>
          let bucket := PArray.get a pos in
          let pos := (pos - 1)%uint63 in
          go n pos (read_bytes 7 bucket acc)
      end
  in
  let acc := go (int_to_nat r.(R.n)) r.(R.ind) acc in
  match r.(R.underhang) with
  | Some u =>
      let bucket := PArray.get a (u.(U.ind)) in
      read_bytes (int_to_nat u.(U.n)) bucket acc
  | None => acc
  end.

Definition print_sub s from len :=
  let a := s.(smallstr_bytes) in
  let slen := get a 0%uint63 in
  print_sub_aux a from (if Uint63.ltb slen (from+len) then slen else (from+len))%uint63.

Definition print s : list byte :=
Eval lazy beta fix match delta [print_sub] in
  print_sub s 0 (len s).

Definition to_Ns s : list N :=
  List.map (Byte.to_N) (print s).

(* Eval lazy in print_aux_new (parse [x61;x62;x63;x64;x65;x66;x67;x68]).(smallstr_bytes) 0 8. *)

#[local] Notation teststr := (parse (repeat x61 1000)).
Instructions Eval lazy in
  PArray.get teststr.(smallstr_bytes) 0.
Instructions Eval vm_compute in
  PArray.get teststr.(smallstr_bytes) 0.

#[local] Example teststr_comp := Eval vm_compute in parse (repeat x61 1000).

Instructions Eval lazy in
  List.length (print teststr_comp).
Instructions Eval vm_compute in
  List.length (print teststr_comp).


(* [set s i b] sets byte [i] to value [b] in string [s]. Returns [s] unchanged if [i] is bigger or equal to the [len s]. *)
Definition set_byte s i (b : byte) :=
  if (Uint63.leb (len s) i) then s
  else
    let '{|smallstr_bytes := a|} := s in
    let (pos, sh) := position i in
    let bucket := PArray.get a pos in
    let bucket := ((bucket land zero_mask sh) lxor (to_int b << (sh * 8)))%uint63 in
    let a := PArray.set a pos bucket in
    {|smallstr_bytes := a|}.

Eval lazy in print (set_byte (parse (repeat x61 13)) 12 x62).

Fixpoint set_bytes s i (bs : list byte) :=
  match bs with
  | [] => s
  | b :: bs =>
      set_bytes (set_byte s i b) (i+1)%uint63 bs
  end.

Eval lazy in print (set_bytes (parse (repeat x61 13)) 11 [x62;x63]).

(* [extend s n] extends [s] by [n] many zero bytes. *)
Definition extend s (n : int) :=
  if Uint63.eqb n 0 then s else
  let '{|smallstr_bytes := a|} := s in
  let slen := len s in
  let (q, r) := diveucl slen 7 in
  let cap := (7-r)%uint63 in
  let total := (slen + n)%uint63 in
  if Uint63.leb n cap then
    {|smallstr_bytes := PArray.set a 0 total|}
  else
    let newlen := (1+div_up total 7)%uint63 in
    let out := PArray.make newlen 0%uint63 in
    (* TODO: [foldl_i] with offset to skip first item *)
    let out := PArray.foldl_i (fun i v out => PArray.set out i v) a out in
    (* fix length *)
    let out := PArray.set out 0 total in
    Smallstr out.

(* [shrink s n] masks out all but the first [n] elements in [s].
   Only allocates if [n] is smaller than the current length.
 *)
Definition shrink s (n : int) :=
  let '{|smallstr_bytes := a|} := s in
  let slen := len s in
  if Uint63.leb slen n then
    s (* we already no more than [n] elements *)
  else
    let last := div_up n 7 in
    let newlen := (1+last)%uint63 in
    let partial := (Uint63.mod n 7)%uint63 in
    let out := PArray.make newlen 0%uint63 in
    let out := PArray.foldl_i (fun i _ out => PArray.set out i (PArray.get a i)) out out in
    let out := PArray.set out 0 n in
    let out :=
      if Uint63.eqb partial 0 then out else
      PArray.set out last (PArray.get out last land zero_masks_suff (7-partial))%uint63
    in
    Smallstr out.

Eval lazy in print (shrink (parse ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"]%byte) 9).

Definition concat s1 ss :=
  let lens := List.fold_left (fun t s => Uint63.add t (len s)) ss 0%uint63 in
  if Uint63.eqb lens 0 then s1 else
  let out := extend s1 lens in
  let go :=
    fix go offset ss out :=
      match ss with
      | s :: ss =>
          let out := set_bytes out offset (print s) in
          go (offset + len s)%uint63 ss out
      | [] => out
      end
  in
  go (len s1) ss out.

Eval lazy in print (concat (parse ["x";"y";"z"]%byte) [(parse (repeat x61 5)); (parse (repeat x62 5))]).

Definition append s1 s2 :=
  concat s1 [s2].

Eval lazy in append (parse (repeat x61 5)) (parse (repeat x62 5)).
Eval lazy in print (append (parse (repeat x61 5)) (parse (repeat x62 5))).

(* [sub s start l] returns a new string that contains bytes [start .. start+l-1] of [s].
   If [start+l-1] is bigger than [len s], the result is truncated to bytes [start .. len s].
 *)
Definition sub s start l :=
  let len := len s in
  if Uint63.eqb start 0 && Uint63.eqb l len then s else
  if Uint63.leb len start then Smallstr (PArray.make 1%uint63 0%uint63) else
  let '{|smallstr_bytes := a|} := s in
  let rem := (len-start)%uint63 in
  let newlen := if Uint63.leb l rem then l else rem in
  let last := div_up newlen 7 in
  let newarrlen := (1+last)%uint63 in
  let out := PArray.make newarrlen 0%uint63 in
  let bytes := print_sub_aux a start l in
  let out := Smallstr (PArray.set out 0 newlen) in
  let out := List.fold_left (fun '(i, out) b => ((i+1)%uint63, set_byte out i b)) bytes (0%uint63,out) in
  out.2.

Eval lazy in print (sub (parse ["a"; "b"; "c"; "d"]%byte) 1 4).


Import BinInt.


#[global] String Notation SmallStr.smallstr SmallStr.parse SmallStr.print : smallstr_scope.

Definition compare s1 s2 :=
  (PArray.compare (cmp:=Uint63.compare) s1.(smallstr_bytes) s2.(smallstr_bytes)).

Definition lt s1 s2 :=
  @PArray.lt _ eq (fun x y => to_Z x < to_Z y)%Z (fun x y => to_Z x > to_Z y)%Z
             s1.(smallstr_bytes) s2.(smallstr_bytes).

Lemma eq'_eq (a1 a2 : array _) :
  (@eq' _ eq (fun x y => to_Z x < to_Z y)%Z (fun x y => to_Z x > to_Z y)%Z) a1 a2 <-> a1 = a2.
Proof.
  split.
  - inversion 1. apply array_ext => //. rewrite !default_get !H1 H0 //.
  - move => ->. by constructor.
Qed.

Instance Uint63_spec_compare_Z x y:
  SpecCompare (x = y) (to_Z x < to_Z y)%Z (to_Z x > to_Z y)%Z (x ?= y)%uint63.
Proof.
  rewrite Uint63.compare_spec.
  constructor; case Z.compare_spec => //=; lia.
Qed.

Existing Class CompareSpec.
Existing Instance Uint63.compare_spec_Z.

Lemma uint63_compare_swap :
  ∀ x y : int, inv (x ?= y)%uint63 = (y ?= x)%uint63.
Proof.
  intros. rewrite !Uint63.compare_spec.
  do 2!case: Z.compare_spec => //=; lia.
Qed.

#[global] Instance compare_spec s1 s2 : CompareSpec (s1 = s2) (lt s1 s2) (lt s2 s1) (compare s1 s2).
Proof.
  destruct s1 as [a1], s2 as [a2] => /=.
  rewrite /lt/gt /compare /=.
  induction (PArray.compare_spec _ _ a1 a2); constructor; auto.
  - f_equal. by apply eq'_eq.
  - apply/rel_cmp_iff.
    suff ->: Lt = PArray.compare (cmp:=Uint63.compare) a2 a1.
    { apply pre_rel_spec. }
    symmetry.
    apply sc_gt in H.
    rewrite compare_swap.
    { by case: PArray.compare H. }
    apply uint63_compare_swap.
Qed.


#[global] Instance spec_compare s1 s2 : SpecCompare (s1 = s2) (lt s1 s2) (lt s2 s1) (compare s1 s2).
Proof.
  destruct s1 as [a1], s2 as [a2] => /=.
  constructor.
  - injection 1. rewrite /compare /= => H1. apply sc_eq. by apply/eq'_eq.
  - rewrite /lt. move/rel_cmp_iff/spec_pre_rel => //=.
  - rewrite /lt /compare. move/rel_cmp_iff/spec_pre_rel => //= H.
    rewrite PArray.compare_swap -?H //.
    apply uint63_compare_swap.
Qed.

#[global] Instance lt_Irreflexive : Irreflexive lt.
Proof.
  intros s => +.
  unfold lt,compare.
  inversion 1; lia.
Qed.

(* #[global] Instance : Transitive gt. *)
(* Proof. *)
(*   intros [a1] [a2] [a3]. *)
(*   rewrite /gt /compare /=. *)
(*   have H: forall x y, Uint63.compare x y = inv (Uint63.compare y x). *)
(*   { intros. rewrite !Uint63.compare_spec. repeat case : Z.compare_spec => //=; lia. } *)
(*   move/(compare_swap_aux H) => ?. *)
(*   move/(compare_swap_aux H) => ?. *)
(*   apply (compare_swap_aux H). *)
(*   cbn in *. *)
(*   apply (lt_Transitive (Smallstr a3) (Smallstr a2) (Smallstr a1)) => //. *)
(* Qed. *)

#[local] Definition to_list (s : smallstr) : (int * list Uint63.int) :=
  PArray.to_list (s.(smallstr_bytes)).

#[local] Definition of_list (l : int * list Uint63.int) : option smallstr :=
  match PArray.of_list l with Some a => Some (Smallstr a) | _ => None end.

#[global,program] Instance smallstr_countable : Countable smallstr :=
  { encode s := encode s.(smallstr_bytes);
    decode l := option_map (Smallstr) (decode l)
  }.
Next Obligation.
  move => [a].
  by rewrite decode_encode.
Qed.
End SmallStr.

#[global] Bind Scope smallstr_scope with SmallStr.t.
#[global] String Notation SmallStr.smallstr SmallStr.parse SmallStr.print : smallstr_scope.

#[global] Infix "++" := (SmallStr.append) : smallstr_scope.

Eval cbv in "ab"%smallstr.(SmallStr.smallstr_bytes).

Eval cbv in SmallStr.set_byte "test"%smallstr 3 x61.

(* Unset Printing Notations. *)
Eval lazy in SmallStr.smallstr_bytes "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".

Instructions Eval lazy in SmallStr.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf" "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".
(*  9788956 *)
(* 15416266 *)
Instructions Eval vm_compute in SmallStr.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf" "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".
(*  8146865 *)
(* 14891156 *)


Module Type TEST.
  Import Coq.Strings.String.
  Definition sanity (s : string) :=
    if String.eqb (string_of_list_byte (SmallStr.print (SmallStr.parse (list_byte_of_string s)))) s then True else False.

  Succeed Example _1 : sanity "a" := I.
  Succeed Example _1 : sanity "ab" := I.
  Succeed Example _1 : sanity "abc" := I.
  Succeed Example _1 : sanity "abcd" := I.
  Succeed Example _1 : sanity "abcde" := I.
  Succeed Example _1 : sanity "abcdef" := I.
  Succeed Example _1 : sanity "abcdefg" := I.
  Succeed Example _1 : sanity "abcdefg" := I.
  Succeed Example _1 : sanity "abcdefgh" := I.
  Succeed Example _1 : sanity "abcdefghi" := I.
  Example _1 : sanity "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf" := I.

Instructions Eval lazy in String.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string.
(* 15418213 *)

Instructions Eval vm_compute in String.eqb "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf"%string.
(* 14892062 *)

  Time Eval vm_compute in sanity "abcdefghi000000adkfjadsfkjasdfkjasd;fkljads;fkjladsfadsfadsfadsf".
 (* 60175911 *)
 (* 9256064  *)
End TEST.


Module OT_SmallStr <: OrderedType.OrderedType.
  Definition t := SmallStr.t.
  Definition eq := @eq SmallStr.t.
  Definition lt := SmallStr.lt.

  Implicit Types s : SmallStr.t.

  Lemma eq_refl s : eq s s.
  Proof. reflexivity. Qed.
  Lemma eq_sym s1 s2 : eq s1 s2 -> eq s2 s1.
  Proof. by symmetry. Qed.

  Lemma eq_trans s1 s2 s3 : eq s1 s2 -> eq s2 s3 -> eq s1 s3.
  Proof. intros *->->. reflexivity. Qed.

  Lemma lt_trans s1 s2 s3: lt s1 s2 -> lt s2 s3 -> lt s1 s3.
  Proof.
    apply: PArray.lt_Transitive; [|lia..].
    intros x y z ? ?. lia.
  Qed.

  Lemma lt_not_eq : forall (x y : t) (_ : lt x y), not (eq x y).
  Proof. intros * H1 ->. by apply: SmallStr.lt_Irreflexive. Qed.

  #[program]
  Definition compare s1 s2 : Compare lt eq s1 s2 :=
    match SmallStr.compare s1 s2 as c return
          SmallStr.compare s1 s2 = c -> Compare lt eq s1 s2
  with
    | Lt => fun H => LT _
    | Eq => fun H => EQ _
    | Gt => fun H => GT _
    end (Logic.eq_refl (SmallStr.compare s1 s2)).
  Next Obligation. move => ? ?. case: SmallStr.compare_spec => //. Qed.
  Next Obligation. move => ? ?. case: SmallStr.compare_spec => //. Qed.
  Next Obligation. move => ? ?. case: SmallStr.compare_spec => //. Qed.

  #[program]
  Definition eq_dec := SmallStr.eq_dec.
End OT_SmallStr.
