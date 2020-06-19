(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.Lists.List.

From bedrock Require Import ChargeCompat.
From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp.

Section with_Σ.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.
  Variables (M : coPset) (ti : thread_info).

  Local Notation primR := (@primR _ _ resolve) (only parsing).
  Local Notation anyR := (@anyR _ _ resolve) (only parsing).

  (****** Wp Semantics for builtins
   *)
  Parameter wp_builtin :
      forall {resolve:genv}, coPset -> thread_info ->
        BuiltinFn -> type (* the type of the builtin *) ->
        list val -> (val -> mpred) -> mpred.

  Local Notation BUILTIN := (wp_builtin (resolve:=resolve) M ti).

  Axiom wp_unreachable : forall Q,
      False |-- BUILTIN Bin_unreachable (Tfunction Tvoid nil) nil Q.

  Axiom wp_trap : forall Q,
      False |-- BUILTIN Bin_trap (Tfunction Tvoid nil) nil Q.

  Axiom wp_expect : forall exp c Q,
      Q exp |-- BUILTIN Bin_expect (Tfunction (Tint W64 Signed) (Tint W64 Signed :: Tint W64 Signed :: nil)) (exp :: c :: nil) Q.

  (** Bit computations
   *)
  Definition first_set (sz : bitsize) (n : Z) : Z :=
    let n := trim (bitsN sz) n in
    if Z.eqb n 0 then 0
    else
      (fix get ls : Z :=
         match ls with
         | nil => 64
         | l :: ls =>
           if Z.testbit n l
           then 1 + l
           else get ls
         end)%Z (Z.of_nat <$> seq 0 (N.to_nat (bitsN sz))).

  (* Returns one plus the index of the least significant 1-bit of x,
     or if x is zero, returns zero. *)
  Definition ffs_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tint sz Signed) |] ** Q (Vint (first_set sz n)).

  Axiom wp_ffs : forall sz c Q,
          ffs_spec sz c Q
      |-- BUILTIN Bin_ffs (Tfunction (Tint sz Signed) (Tint sz Signed :: nil)) (Vint c :: nil) Q.

  Axiom wp_ffsl : forall sz c Q,
          ffs_spec sz c Q
      |-- BUILTIN Bin_ffsl (Tfunction (Tint sz Signed) (Tint sz Signed :: nil)) (Vint c :: nil) Q.

  Axiom wp_ffsll : forall sz c Q,
          ffs_spec sz c Q
      |-- BUILTIN Bin_ffsll (Tfunction (Tint sz Signed) (Tint sz Signed :: nil)) (Vint c :: nil) Q.

  (* Returns the number of trailing 0-bits in x, starting at the least
     significant bit position. If x is 0, the result is undefined. *)
  Definition trailing_zeros (sz : bitsize) (n : Z) : Z :=
    (fix get ls : Z :=
       match ls with
       | nil => 64
       | l :: ls =>
         if Z.testbit n l
         then l
         else get ls
       end)%Z (Z.of_nat <$> seq 0 (N.to_nat (bitsN sz))).


  Definition ctz_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tint sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (trailing_zeros sz n)).

  Axiom wp_ctz : forall sz c Q,
          ctz_spec sz c Q
      |-- BUILTIN Bin_ctz (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_ctzl : forall sz c Q,
          ctz_spec sz c Q
      |-- BUILTIN Bin_ctzl (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_ctzll : forall sz c Q,
          ctz_spec sz c Q
      |-- BUILTIN Bin_ctzll (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  (* Returns the number of leading 0-bits in x, starting at the most significant
     bit position. If x is 0, the result is undefined. *)
  Definition leading_zeros (sz : bitsize) (l : Z) : Z :=
    bitsZ sz - Z.log2 (l mod (2^64)).

  Definition clz_spec (sz : bitsize) (n : Z) (Q : val -> mpred) : mpred :=
    [| has_type (Vint n) (Tint sz Unsigned) |] ** [| n <> 0 |] ** Q (Vint (leading_zeros sz n)).

  Axiom wp_clz : forall sz c Q,
          clz_spec sz c Q
      |-- BUILTIN Bin_clz (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_clzl : forall sz c Q,
          clz_spec sz c Q
      |-- BUILTIN Bin_clzl (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  Axiom wp_clzll : forall sz c Q,
          clz_spec sz c Q
      |-- BUILTIN Bin_clzll (Tfunction (Tint sz Unsigned) (Tint sz Unsigned :: nil)) (Vint c :: nil) Q.

  (* Returns x with the order of the bytes reversed; for example, 0xaabb becomes
     0xbbaa. Byte here always means exactly 8 bits. *)
  Local Definition bswap16 (n : Z) : Z :=
    Z.lor (Z.shiftl (Z.land n 255) 8) (Z.land (Z.shiftr n 8) 255).
  Local Definition bswap32 (n : Z) : Z :=
    let low := bswap16 n in
    let high := bswap16 (Z.shiftr n 16) in
    Z.lor (Z.shiftl low 16) high.
  Local Definition bswap64 (n : Z) : Z :=
    let low := bswap32 n in
    let high := bswap32 (Z.shiftr n 32) in
    Z.lor (Z.shiftl low 32) high.
  Local Definition bswap128 (n : Z) : Z :=
    let low := bswap64 n in
    let high := bswap64 (Z.shiftr n 64) in
    Z.lor (Z.shiftl low 64) high.

  Definition bswap (sz : bitsize) : Z -> Z :=
    match sz with
    | W8 => id
    | W16 => bswap16
    | W32 => bswap32
    | W64 => bswap64
    | W128 => bswap128
    end.

  Local Definition bytes (ls : list Z) :=
    fold_left (fun a b => a * 256 + b)%Z ls 0.
  Arguments bytes _%Z.

  Local Definition _bswap16_test : bswap W16 (bytes (1::2::nil)%Z) = bytes (2::1::nil)%Z := eq_refl.
  Local Definition _bswap32_test :
    bswap W32 (bytes (1::2::3::4::nil)%Z) = bytes (4::3::2::1::nil)%Z := eq_refl.
  Local Definition _bswap64_test :
    bswap W64 (bytes (1::2::3::4::5::6::7::8::nil)%Z) = bytes (8::7::6::5::4::3::2::1::nil)%Z := eq_refl.

  Axiom wp_bswap16 : forall x Q,
          [| has_type (Vint x) (Tint W16 Unsigned) |] ** Q (Vint (bswap W16 x))
      |-- BUILTIN Bin_bswap16 (Tfunction (Tint W16 Unsigned) (Tint W16 Unsigned :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap32 : forall x Q,
          [| has_type (Vint x) (Tint W32 Unsigned) |] ** Q (Vint (bswap W32 x))
      |-- BUILTIN Bin_bswap32 (Tfunction (Tint W32 Unsigned) (Tint W32 Unsigned :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap64 : forall x Q,
          [| has_type (Vint x) (Tint W64 Unsigned) |] ** Q (Vint (bswap W64 x))
      |-- BUILTIN Bin_bswap64 (Tfunction (Tint W64 Unsigned) (Tint W64 Unsigned :: nil))
          (Vint x :: nil) Q.

  Axiom wp_bswap128 : forall x Q,
          [| has_type (Vint x) (Tint W128 Unsigned) |] ** Q (Vint (bswap W128 x))
      |-- BUILTIN Bin_bswap128 (Tfunction (Tint W128 Unsigned) (Tint W128 Unsigned :: nil))
          (Vint x :: nil) Q.

End with_Σ.
