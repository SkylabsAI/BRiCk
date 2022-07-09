Require Import Coq.ZArith.ZArith.
Require Import Flocq.IEEE754.Bits.
Require Import Flocq.IEEE754.Binary.

(* parameters for *)
Record rep_param : Set :=
{ f_prec : Z
; f_ebits : Z
; f_emax := Z.pow 2 f_ebits
; f_prec_ok : FLX.Prec_gt_0 f_prec
; f_emax_ok : BinarySingleNaN.Prec_lt_emax f_prec f_emax
}.

Definition ftype (p : rep_param) : Set :=
  binary_float p.(f_prec) p.(f_emax).

#[program]
Definition default_nan (p : rep_param) : ftype p :=
  B754_nan _ _ false (Zaux.iter_nat xO (Z.to_nat (p.(f_prec) - 2)%Z) 1%positive) _.
Next Obligation. Admit Obligations.
Lemma default_nan_is_nan : forall p, is_nan _ _ (default_nan p) = true.
Proof. Admitted.

Definition binop_nan (p : rep_param) (l r : ftype p)
  : {x1 : ftype p | is_nan p.(f_prec) p.(f_emax) x1 = true} :=
  match l , r with
  | B754_nan _ _ a b c , _ => exist _ (B754_nan _ _ a b c) eq_refl
  | _ , B754_nan _ _ a b c => exist _ (B754_nan _ _ a b c) eq_refl
  | _ , _ => exist _ (default_nan p) (default_nan_is_nan _)
  end.

Record op_param : Set :=
{ o_rep :> rep_param
; o_do_nan : (ftype o_rep -> ftype o_rep -> {x1 : ftype o_rep | is_nan o_rep.(f_prec) o_rep.(f_emax) x1 = true})
}.

Definition op_default (p : rep_param) : op_param :=
  {| o_rep := p
   ; o_do_nan := binop_nan p |}.

Definition r_float32 : rep_param :=
  {| f_prec := 24
   ; f_ebits := 7
   ; f_prec_ok := eq_refl
   ; f_emax_ok := eq_refl |}.
Definition float32 : op_param :=
  {| o_rep := r_float32
   ; o_do_nan := binop_nan_pl32 |}.

Definition r_float64 : rep_param :=
  {| f_prec := 53
   ; f_ebits := 10
   ; f_prec_ok := eq_refl
   ; f_emax_ok := eq_refl |}.
Definition float64 : op_param :=
  {| o_rep := r_float64
   ; o_do_nan := binop_nan_pl64 |}.


Definition r_float128 : rep_param :=
  {| f_prec := 113
   ; f_ebits := 15
   ; f_prec_ok := eq_refl
   ; f_emax_ok := eq_refl |}.
Definition float128 := op_default r_float128.

Require Import stdpp.decidable.
Require Import stdpp.numbers.
Axiom todo : forall t, t.
Require Import Coq.micromega.Lia.
Definition through_dec `{d : Decision P} : P :=
  match decide P with
  | left pf => pf
  | _ => todo _
  end.
Definition fparse (p : rep_param) : Z -> ftype p.
  destruct p; simpl. unfold ftype; simpl. unfold f_emax, f_ebits.
  generalize (binary_float_of_bits (f_prec0 - 1) (f_ebits0 + 1)).
  replace (f_prec0 - 1 + 1)%Z with f_prec0 by eapply through_dec.
  replace (f_ebits0 + 1 - 1)%Z with f_ebits0 by eapply through_dec.
  intro X; apply X.
  all: eapply through_dec.
Defined.

Definition from_hex_digit (s : Byte.byte) : Z :=
  match s with
  | Byte.x30 => 0
  | Byte.x31 => 1
  | Byte.x32 => 2
  | Byte.x33 => 3
  | Byte.x34 => 4
  | Byte.x35 => 5
  | Byte.x36 => 6
  | Byte.x37 => 7
  | Byte.x38 => 8
  | Byte.x39 => 9
  | Byte.x61 => 10
  | Byte.x62 => 11
  | Byte.x63 => 12
  | Byte.x64 => 13
  | Byte.x65 => 14
  | Byte.x66 => 15
  | Byte.x41 => 10
  | Byte.x42 => 11
  | Byte.x43 => 12
  | Byte.x44 => 13
  | Byte.x45 => 14
  | Byte.x46 => 15
  | _ => 0
  end.

Require Import bedrock.prelude.bytestring.
Fixpoint from_bits (acc : Z) (s : BS.t) : Z :=
  match s with
  | BS.EmptyString => acc
  | BS.String a b => from_bits (acc * 16 + from_hex_digit a) b
  end.

Eval compute in from_bits 0 "100"%bs.



Require Import Flocq.Core.Digits.
Eval vm_compute in
  bits_of_binary_float (float64.(f_prec) - 1) (float64.(f_ebits) + 1) $ fparse float64 (from_bits 0 "90ccccccccccd33").

Definition fadd (p : op_param) : BinarySingleNaN.mode -> ftype p -> ftype p -> ftype p :=
  Bplus p.(f_prec) p.(f_emax) p.(f_prec_ok) p.(f_emax_ok) p.(o_do_nan).
Definition fsub (p : op_param) : BinarySingleNaN.mode -> ftype p -> ftype p -> ftype p :=
  Bminus p.(f_prec) p.(f_emax) p.(f_prec_ok) p.(f_emax_ok) p.(o_do_nan).
Definition fmul (p : op_param) : BinarySingleNaN.mode -> ftype p -> ftype p -> ftype p :=
  Bmult p.(f_prec) p.(f_emax) p.(f_prec_ok) p.(f_emax_ok) p.(o_do_nan).
Definition fdiv (p : op_param) : BinarySingleNaN.mode -> ftype p -> ftype p -> ftype p :=
  Bdiv p.(f_prec) p.(f_emax) p.(f_prec_ok) p.(f_emax_ok) p.(o_do_nan).
