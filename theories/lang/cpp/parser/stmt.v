(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.bytestring.
Require Import bedrock.lang.cpp.parser.prelude.

#[local] Open Scope bs_scope.

(* TODO: remove these next definitiosn when we drop [DTOR] *)
Fixpoint do_end (ty : bs) : bs :=
  match ty with
  | BS.String _ BS.EmptyString => "D0Ev"
  | BS.String x v => BS.String x (do_end v)
  | _ => BS.EmptyString
  end.

(** Build the name of a destructor for a type.
    NOTE this can be improved if we essentially turn it into a
    constructor of [obj_name]; however, that has some wider
    implications that we should solve in a separate issue.
 *)
Definition DTOR (ty : bs) : bs :=
  match ty with
  | BS.String _ (BS.String _ ((BS.String c _) as rest)) =>
      if bool_decide (c = "N"%byte) then
        "_Z" ++ do_end rest
      else
        "_ZN" ++ rest ++ "D0Ev"
  | BS.String _ (BS.String _ v) => "_ZN" ++ do_end v
  | _ => "OOPS"
  end%bs.

Section stmt.
  Context {lang : lang.t}.
  #[local] Notation Expr := (Expr' lang).
  #[local] Notation Stmt := (Stmt' lang).

  Definition Sreturn_void : Stmt := Sreturn None.
  Definition Sreturn_val (e : Expr) : Stmt := Sreturn (Some e).
  Definition Sforeach (range ibegin iend : Stmt)
    (init : option Stmt) (cond : option Expr) (inc : option Expr)
    (decl body : Stmt) : Stmt :=
    Sseq [range; ibegin; iend; Sfor init cond inc (Sseq [decl; body])].
End stmt.
