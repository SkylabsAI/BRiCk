(*
 * Copyright (c) 2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import ExtLib.Programming.Show.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.bytestring_core.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.upoly.base.
Require Import bedrock.upoly.upoly.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.pretty.

(* UPSTREAM? *)
Module showN.
  Definition bs_ShowScheme : ShowScheme bs :=
    {| show_mon := {| Monoid.monoid_plus := BS.append ; Monoid.monoid_unit := BS.EmptyString |}
    ; show_inj a := BS.String (Ascii.byte_of_ascii a) BS.EmptyString |}.

  Definition showN (n : N) : bs := runShow (M:=bs_ShowScheme) (show $ N.to_nat n).
End showN.

(** Pretty printing of C++ names
    This printer is quite similar to the <pretty.v> printer, but this one is more
    restricted becuase it is important that this function is invertible by the parser
    in <parser.v>.
 *)
Section with_lang.
  Import UPoly.
  #[local] Open Scope bs_scope.
  Fixpoint sepBy (sep : bs) (ls : list bs) : bs :=
    match ls with
    | nil => ""
    | l :: nil => l
    | l :: ls => l ++ sep ++ sepBy sep ls
    end.
  Definition parens (b : bs) : bs := "(" ++ b ++ ")".
  Definition angles (b : bs) : bs := "<" ++ b ++ ">".

  #[local] Open Scope bs_scope.

  Definition prefix : bs -> bs -> bs := BS.append.
  Definition postfix (a b : bs) : bs := BS.append b a.

  Section atomic_name.
    Context {type Expr : Set} (printType : type -> option bs) (printExpr : Expr -> option bs).
    Variable top : option bs.

    Definition printFN (fn : function_name_ type) : option bs :=
      match fn with
      | Nf nm => mret nm
      | Nctor =>
          match top with
          | None => mfail
          | Some cls => mret cls
          end
      | Ndtor =>
          match top with
          | None => mfail
          | Some cls => mret $ "~" ++ cls
          end
      | Nop o =>
          match o with
          | OONew _ | OODelete _ | OOCoawait =>
            mret $ "operator " ++ printOO o
          | _ => mret $ "operator" ++ printOO o
          end
      | Nop_conv t => prefix "operator " <$> printType t
      | Nop_lit i => mret $ "operator """"_" ++ i
      | Nunsupported_function note => mfail
      end.

    Definition printFQ (fq : function_qualifier) : bs :=
      match fq with
      | Nconst => "const"
      | Nvolatile => "volatile"
      | Nnoexcept => "noexcept"
      | Nlvalue => "&"
      | Nrvalue => "&&"
      end.

    #[local] Open Scope monad_scope.
    Definition printAN (an : atomic_name_ type) : option bs :=
      match an with
      | Nid id => mret id
      | Nfunction quals nm args =>
          let* nm := printFN nm in
          let* args := traverse (F:=eta option) printType args in
          let quals := fmap (M:=eta list) printFQ quals in
          mret $ nm ++ parens (sepBy ", " args) ++
                  match quals with
                  | [] => ""
                  | _ => sepBy " " quals
                  end
      | Nclosure types =>
          (fun t => parens $ sepBy ". " t) <$> traverse (T:=eta list) (F:=eta option) printType types
      | Nanon n => mret $ "#" ++ showN n
      | Nunsupported_atomic note => mfail
      end%bs.
  End atomic_name.

  Fixpoint topName (nm : name) : option bs :=
    match nm with
    | Nglobal (Nid id) => Some id
    | Nscoped _ (Nid id) => Some id
    | Ninst nm _ => topName nm
    | _ => None
    end.

  Definition printUO (o : overloadable.RUnOp) : bs :=
    match o with
    | overloadable.Rpreinc => "(++_)"
    | overloadable.Rpostinc => "(_++)"
    | overloadable.Rpredec => "(--_)"
    | overloadable.Rpostdec => "(_--)"
    | overloadable.Rstar => "*"
    | overloadable.Rarrow => "->"
    | overloadable.Runop op =>
        match op with
        | Uminus => "-"
        | Uplus => "+"
        | Unot => "!"
        | Ubnot => "~"
        | Uunsupported n => n
        end
    end.

  Definition printBO (o : overloadable.RBinOp) : option bs :=
    let printBO o :=
      match o with
      | Badd => mret "+"
      | Band => mret "&&"
      | Bcmp => mret "<=>"
      | Bdiv => mret "/"
      | Beq => mret "=="
      | Bge => mret ">="
      | Bgt => mret ">"
      | Ble => mret "<="
      | Blt => mret "<"
      | Bmul => mret "*"
      | Bneq => mret "!="
      | Bor => mret "||"
      | Bmod => mret "%"
      | Bshl => mret "<<"
      | Bshr => mret ">>"
      | Bsub => mret "-"
      | Bxor => mret "^"
      | Bdotp => mret ".*"
      | Bdotip => mret "->*"
      | Bunsupported b => mfail
      end
    in
    match o with
    | overloadable.Rbinop b => printBO b
    | overloadable.Rassign => mret "="
    | overloadable.Rassign_op b => (fun a => a ++ "=") <$> printBO b
    | overloadable.Rsubscript => mret "[]"
    end.

  Fixpoint printN (nm : name) : option bs :=
    match nm with
    | Nglobal an => printAN printT None an
    | Ndependent an => printT an
    | Nscoped base n => (fun b n => b ++ "::" ++ n) <$> printN base <*> printAN printT (topName base) n
    | Ninst base i =>
        let printTA ta :=
          match ta with
          | Atype t => printT t
          | Avalue e => printE e
          | Aunsupported note => mfail
          end
        in
        (fun n tas => n ++ angles (sepBy ", " tas)) <$> printN base <*> traverse printTA i
    | Nunsupported note => mfail
    end

  with printT (ty : type) : option bs :=
    match ty with
    | Tint => mret "int"
    | Tuint => mret "unsigned int"
    | Tchar => mret "char"
    | Tuchar => mret "unsigned char"
    | Tschar => mret "signed char"
    | Tshort => mret "short"
    | Tushort => mret "unsigned short"
    | Tlong => mret "long"
    | Tulong => mret "unsigned long"
(*    | Tlonglong => mret "long long"
    | Tulonglong => mret "unsigned long long" *)
    | Tnum W128 Signed => mret "int128_t"
    | Tnum W128 Unsigned => mret "uint128_t"
    | Twchar => mret "wchar_t"
    | Tchar8 => mret "char8_t"
    | Tchar16 => mret "char16_t"
    | Tchar32 => mret "char32_t"
    | Tfloat => mret "float"
    | Tfloat16 => mret "float16"
    | Tfloat128 => mret "float128"
    | Tdouble => mret "double"
    | Tlongdouble => mret "long double"
    | Tbool => mret "bool"
    | Tnullptr => mret "nullptr_t"
    | Tptr t => postfix "*" <$> printT t
    | Tref t => postfix "&" <$> printT t
    | Trv_ref t => postfix "&&" <$> printT t
    | Tmember_pointer cls t => (fun t c => t ++ " " ++ c ++ "::*") <$> printT t <*> printT cls
    | Tqualified _ (Tqualified _ _) => mfail
    | Tqualified q t =>
        (fun t => sepBy " " $ (t :: (if q_const q then ["const"] else []) ++
        (if q_volatile q then ["volatile"] else []))%list) <$> printT t
    | Tvoid => mret "void"
    | Tarray t n => (fun t => t ++ "[" ++ showN n ++ "]") <$> printT t
    | Tincomplete_array t => postfix "[]" <$> printT t
    | Tvariable_array t e => (fun t n => t ++ "[" ++ n ++ "]") <$> printT t <*> printE e
    | Tdecltype e => mfail (* (fun e => "decltype((" ++ e ++ "))") <$> printE e *)
    | Texprtype e => mfail (* (fun e => "decltype(" ++ e ++ ")") <$> printE e *)
    | Tnamed nm => printN nm
    | Tenum nm => prefix "#" <$> printN nm
    | Tfunction ft =>
        let add_dots (ls : list bs) :=
          match ft.(ft_arity) with
          | Ar_Variadic => (ls ++ ["..."])%list
          | _ => ls
          end
        in
        if ft.(ft_cc) is CC_C then
          (fun t tas => parens (t ++ "*") ++ parens (sepBy ", " $ add_dots tas))
            <$> printT ft.(ft_return)
            <*> traverse (T:=eta list) (F:=eta option) printT ft.(ft_params)
        else mfail
    | Tarch _ note => mfail
    | Tunsupported note => mfail
    | Tparam nm => mret $ "$" ++ nm
    | _ => mfail
    end

  with printE (e : Expr) : option bs :=
    match e with
    | Eglobal nm _ => printN nm
    | _ => mfail
    end.

End with_lang.

Definition print_name (input : name) : option (list Byte.byte) :=
  BS.print <$> printN input.
