(*
 * Copyright (c) 2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.prelude.base.
Require Import bluerock.prelude.pstring.

Require Import bluerock.lang.cpp.syntax.core.

(** Pretty printing of C++ terms *)

#[local] Open Scope pstring_scope.

Definition printOO (oo : OverloadableOperator) : PrimString.string :=
  match oo with
  | OOTilde => "~"
  | OOExclaim => "!"
  | OOPlusPlus => "++"
  | OOMinusMinus => "--"
  | OOStar => "*"
  | OOPlus => "+"
  | OOMinus => "-"
  | OOSlash => "/"
  | OOPercent => "%"
  | OOCaret => "^"
  | OOAmp => "&"
  | OOPipe => "|"
  | OOEqual => "="
  | OOLessLess => "<<"
  | OOGreaterGreater => ">>"
  | OOPlusEqual => "+="
  | OOMinusEqual => "-="
  | OOStarEqual => "*="
  | OOSlashEqual => "/="
  | OOPercentEqual => "%="
  | OOCaretEqual => "^="
  | OOAmpEqual => "&="
  | OOPipeEqual => "|="
  | OOLessLessEqual => "<<="
  | OOGreaterGreaterEqual => ">>="
  | OOEqualEqual => "=="
  | OOExclaimEqual => "!="
  | OOLess => "<"
  | OOGreater => ">"
  | OOLessEqual => "<="
  | OOGreaterEqual => ">="
  | OOSpaceship => "<=>"
  | OOComma => ","
  | OOArrowStar => "->*"
  | OOArrow => "->"
  | OOSubscript => "[]"
  | OOAmpAmp => "&&"
  | OOPipePipe => "||"
  | OONew array => if array then " new[]" else " new"
  | OODelete array => if array then " delete[]" else " delete"
  | OOCall => "()"
  | OOCoawait => " coawait"
  end.

Section with_lang.

  Definition showN (n : N) : PrimString.string :=
    pstring.N.to_string n.
  Definition showZ (z : Z) : PrimString.string :=
    match z with
    | Z0 => "0"
    | Zpos p => showN (Npos p)
    | Zneg p => "-" ++ showN (Npos p)
    end.

  Definition parens (b : PrimString.string) : PrimString.string := "(" ++ b ++ ")".
  Definition angles (b : PrimString.string) : PrimString.string := "<" ++ b ++ ">".
  Fixpoint sepBy (sep : PrimString.string) (ls : list PrimString.string) : PrimString.string :=
    match ls with
    | [] => ""
    | l :: [] => l
    | l :: ls => l ++ sep ++ sepBy sep ls
    end.

  Section atomic_name.
    Context {type Expr : Set} (printType : type -> PrimString.string) (printExpr : Expr -> PrimString.string).
    Variable top : option PrimString.string.

    Definition with_space (b : PrimString.string) : PrimString.string :=
      if bool_decide (b = "") then "" else " " ++ b.

    Definition printFQ (fq : function_qualifiers.t) : PrimString.string :=
      let c := if function_qualifiers.is_const fq then ["const"] else [] in
      let v := if function_qualifiers.is_volatile fq then ["volatile"] else [] in
      let vc := match function_qualifiers.vc_of fq with
                | Prvalue => []
                | Lvalue => ["&"]
                | Xvalue => ["&&"]
                end in
      concat $ join_sep " " $ (c ++ v ++ vc)%list.

    Definition printAN (an : atomic_name_ type) : PrimString.string :=
      let print_args args := parens $ concat $ join_sep ", " $ printType <$> args in
      match an with
      | Nid id => id
      | Nfunction quals nm args =>
          nm ++ print_args args ++ with_space (printFQ quals)
      | Nctor args =>
          match top with
          | None => "<ctor>"
          | Some cls => cls
          end ++ print_args args
      | Ndtor =>
          match top with
          | None => "<dtor>"
          | Some cls => "~" ++ cls
          end
      | Nop q o args =>
          "operator" ++ printOO o ++ print_args args ++ with_space (printFQ q)
      | Nop_conv q t => "operator " ++ printType t ++ "()" ++ with_space (printFQ q)
      | Nop_lit i args => "operator """"_" ++ i ++ print_args args
      | Nanon n => "@" ++ showN n
      | Nanonymous => "(anon)"
      | Nfirst_decl n => "#" ++ n
      | Nfirst_child n => "." ++ n
      | Nunsupported_atomic note => "?" ++ note
      end.
  End atomic_name.

  Fixpoint topName (nm : name) : option PrimString.string :=
    match nm with
    | Nglobal (Nid id) => Some id
    | Nscoped _ (Nid id) => Some id
    | Ninst nm _ => topName nm
    | _ => None
    end.

  Definition printUO (o : overloadable.RUnOp) : PrimString.string :=
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

  Definition printBO (o : overloadable.RBinOp) : PrimString.string :=
    let printBO o :=
      match o with
      | Badd => "+"
      | Band => "&&"
      | Bcmp => "<=>"
      | Bdiv => "/"
      | Beq => "=="
      | Bge => ">="
      | Bgt => ">"
      | Ble => "<="
      | Blt => "<"
      | Bmul => "*"
      | Bneq => "!="
      | Bor => "||"
      | Bmod => "%"
      | Bshl => "<<"
      | Bshr => ">>"
      | Bsub => "-"
      | Bxor => "^"
      | Bdotp => ".*"
      | Bdotip => "->*"
      | Bunsupported b => b
      end
    in
    match o with
    | overloadable.Rbinop b => printBO b
    | overloadable.Rassign => "="
    | overloadable.Rassign_op b => printBO b ++ "="
    | overloadable.Rsubscript => "[]"
    end.

  Definition escape_char (n : N) : PrimString.string :=
    match n with
    | 0 => "\0"   (* Null *)
    | 7 => "\a"   (* Alert/Bell *)
    | 8 => "\b"   (* Backspace *)
    | 9 => "\t"   (* Horizontal tab *)
    | 10 => "\n"  (* Line feed/newline *)
    | 11 => "\v"  (* Vertical tab *)
    | 12 => "\f"  (* Form feed *)
    | 13 => "\r"  (* Carriage return *)
    | 34 => "\"""""  (* Double quote *)
    | 39 => "\'"  (* Single quote *)
    | 63 => "\?"  (* Question mark *)
    | 92 => "\\"  (* Backslash *)
    | n =>
        (* For other characters, convert to ASCII if printable, or use hex escape for non-printable *)
        if bool_decide (32 <= n <= 126) then
          (* Printable ASCII range: convert to character *)
          PrimString.make (Evaluate (Uint63Axioms.of_Z 1)) (Uint63Axioms.of_Z (Z.of_N n))
        else
          (* Non-printable: use hex escape sequence \xHH *)
          let d1 := N.modulo (N.div n 16) 16 in
          let d0 := N.modulo n 16 in
          let hex_digit d :=
            match d with
            | 0 => "0"
            | 1 => "1"
            | 2 => "2"
            | 3 => "3"
            | 4 => "4"
            | 5 => "5"
            | 6 => "6"
            | 7 => "7"
            | 8 => "8"
            | 9 => "9"
            | 10 => "a"
            | 11 => "b"
            | 12 => "c"
            | 13 => "d"
            | 14 => "e"
            | _ => "f"
            end
          in
          "\x" ++ hex_digit d1 ++ hex_digit d0
    end%N.

  Definition literal_string_to_string (s : literal_string.t) : PrimString.string :=
    let ps := literal_string.bytes s in
    concat $ foldi (fun _ c cs => escape_char (Z.to_N (Uint63Axioms.to_Z (PrimString.get ps c))) :: cs) ps nil.

  Definition printUO' (uo : UnOp) : PrimString.string :=
    match uo with
    | Uminus => "-"
    | Uplus => "+"
    | Unot => "!"
    | Ubnot => "~"
    | Uunsupported s => "/* " ++ s ++ " */"
    end.
  Definition printBO' (bo : BinOp) : PrimString.string :=
    match bo with
    | Badd => "+"
    | Band => "&"
    | Bcmp => "<=>"
    | Bdiv => "/"
    | Beq => "=="
    | Bge => ">="
    | Bgt => ">"
    | Blt => "<"
    | Ble => "<="
    | Bmul => "*"
    | Bneq => "!="
    | Bor => "|"
    | Bmod => "%"
    | Bshl => "<<"
    | Bshr => ">>"
    | Bsub => "-"
    | Bxor => "^"
    | Bdotp => ".*"
    | Bdotip => "->*"
    | Bunsupported msg => "/* " ++ msg ++ " */"
    end.

  (* TODO: implement this *)
  Definition indent (n : N) (p : PrimString.string) : PrimString.string := p.

  Fixpoint printN (nm : name) : PrimString.string :=
    match nm with
    | Nglobal an => printAN printT None an
    | Ndependent an => printT an
    | Nscoped base Nanonymous => printN base
    | Nscoped base n => printN base ++ "::" ++ printAN printT (topName base) n
    | Ninst base i =>
        printN base ++ angles (concat $ join_sep ", " $ List.concat (List.map printTA i))
    | Nunsupported note => "?" ++ note
    end

  with printTA (ta : temp_arg) : list PrimString.string :=
      match ta with
      | Atype t => [printT t]
      | Avalue e => [printE e]
      | Apack ls => List.concat (List.map printTA ls)
      | Atemplate n => ["<>" ++ printN n]
      | Aunsupported note => [note]
      end

  with printT (ty : type) : PrimString.string :=
    match ty with
    | Tint => "int"
    | Tuint => "unsigned int"
    | Tchar => "char"
    | Tuchar => "unsigned char"
    | Tschar => "signed char"
    | Tshort => "short"
    | Tushort => "unsigned short"
    | Tlong => "long"
    | Tulong => "unsigned long"
    | Tlonglong => "long long"
    | Tulonglong => "unsigned long long"
    | Tnum int_rank.I128 Signed => "int128_t"
    | Tnum int_rank.I128 Unsigned => "uint128_t"
    | Twchar => "wchar_t"
    | Tchar8 => "char8_t"
    | Tchar16 => "char16_t"
    | Tchar32 => "char32_t"
    | Tfloat => "float"
    | Tfloat16 => "float16"
    | Tfloat128 => "float128"
    | Tdouble => "double"
    | Tlongdouble => "long double"
    | Tbool => "bool"
    | Tnullptr => "nullptr_t"
    | Tptr t => printT t ++ "*"
    | Tref t => printT t ++ "&"
    | Trv_ref t => printT t ++ "&&"
    | Tmember_pointer cls t => printT t ++ " " ++ printT cls ++ "::*"
    | Tqualified q t =>
        concat $ join_sep " " $ (printT t :: (if q_const q then ["const"] else []) ++
        (if q_volatile q then ["volatile"] else []))%list
    | Tvoid => "void"
    | Tarray t n => printT t ++ "[" ++ showN n ++ "]"
    | Tincomplete_array t => printT t ++ "[]"
    | Tvariable_array t e => printT t ++ "[" ++ printE e ++ "]"
    | Tdecltype e => "decltype((" ++ printE e ++ "))"
    | Texprtype e => "decltype(" ++ printE e ++ ")"
    | Tnamed nm | Tenum nm => printN nm
    | Tfunction ft =>
        (parens $ printT ft.(ft_return) ++ "*") ++
        (parens $ concat $ join_sep ", " $ printT <$> ft.(ft_params))
    | Tarch _ note => "?" ++ note
    | Tunsupported note => "?" ++ note
    | Tparam nm => nm
    | Tresult_param nm => "decltype(" ++ nm ++ ")"
    | Tresult_global nm => "decltype(" ++ printN nm ++ ")"
    | Tresult_unop op t => "decltype(" ++ printUO op ++ "(?" ++ printT t ++ "))"
    | Tresult_binop op t1 t2 =>
        "decltype(" ++ printBO op ++ "(?" ++ printT t1 ++ ",?" ++ printT t2 ++ "))"
    | Tresult_call _ _
    | Tresult_member_call _ _ _
    | Tresult_parenlist _ _
    | Tresult_member _ _ => "!nyi"
    end

  with printE (e : Expr) : PrimString.string :=
    match e with
    | Eglobal nm _ => printN nm
    | Eparam id => id
    | Eunresolved_global n => printN n
    | Eunresolved_unop op e' =>
        printUO op ++ " " ++ printE e'
    | Eunresolved_binop op e1 e2 =>
      printE e1 ++ " " ++ printBO op ++ " " ++ printE e2
    | Eunresolved_call n args =>
        printN n ++ parens (sepBy "," $ printE <$> args)
    | Eunresolved_member_call n e' args => "nyi!"
    | Eunresolved_parenlist opt_t args => "nyi!"
    | Eunresolved_member e' n =>
        printE e' ++ "." ++ printN n
    | Evar ln t => ln

    | Eenum_const n id =>
        printN n ++ "::" ++ id
    | Eglobal_member n t => "&" ++ printN n
    | Echar num t =>
        "'" ++ escape_char num ++ "'"
    | Estring ls t =>
        """" ++ literal_string_to_string ls ++ """"
    | Eint val t => showZ val
    | Ebool b =>
        if b then "true" else "false"
    | Eunop op e' t =>
        printUO' op ++ printE e'
    | Ebinop op e1 e2 t =>
        printE e1 ++ " " ++ printBO' op ++ " " ++ printE e2
    | Ederef e' t => "*" ++ printE e'
    | Eaddrof e' => "&" ++ printE e'
    | Eassign e1 e2 t => printE e1 ++ " = " ++ printE e2
    | Eassign_op op e1 e2 t => printE e1 ++ " " ++ printBO' op ++ "= " ++ printE e2
    | Epreinc e' t =>
        "++" ++ printE e'
    | Epostinc e' t =>
        printE e' ++ "++"
    | Epredec e' t =>
        "--" ++ printE e'
    | Epostdec e' t =>
        printE e' ++ "--"
    | Eseqand e1 e2 => printE e1 ++ " && " ++ printE e2
    | Eseqor e1 e2 => printE e1 ++ " || " ++ printE e2
    | Ecomma e1 e2 => printE e1 ++ ", " ++ printE e2

    | Ecall e' args =>
        printE e' ++ parens (sepBy "," $ printE <$> args)

    | Eexplicit_cast style t e' =>
        match style with
        | cast_style.functional => printT t ++ "(" ++ printE e' ++ ")"
        | cast_style.c => "(" ++ printT t ++ ")" ++ printE e'
        | cast_style.static => "static_cast<" ++ printT t ++ ">(" ++ printE e' ++ ")"
        | cast_style.const => "const_cast<" ++ printT t ++ ">(" ++ printE e' ++ ")"
        | cast_style.dynamic => "dynamic_cast<" ++ printT t ++ ">(" ++ printE e' ++ ")"
        | cast_style.reinterpret => "reinterpret_cast<" ++ printT t ++ ">(" ++ printE e' ++ ")"
        end
    | Ecast c e' => printE e' (* these casts are implicit *)
    | Emember_ignore is_ptr e1 e2 =>
        printE e1 ++ (if is_ptr then "->" else ".") ++ printE e2
    | Emember_call is_ptr (inl (nm, _, _)) e' args =>
        printE e' ++ (if is_ptr then "->" else ".") ++ printN nm ++ parens (sepBy ", " $ printE <$> args)
    | Emember_call is_ptr (inr e) e' args =>
        printE e' ++ (if is_ptr then "->*" else ".*") ++ printE e' ++ parens (sepBy ", " $ printE <$> args)
    | Eoperator_call op _ [a] => printOO op ++ printE a
    | Eoperator_call op _ [a;b] => printE a ++ " " ++ printOO op ++ " " ++ printE b
    | Esubscript e1 e2 t =>
        printE e1 ++ "[" ++ printE e2 ++ "]"
    | Enull => "nullptr"
    | Esizeof te t' =>
        "sizeof(" ++ match te with
          | inl t => printT t
          | inr e => printE e
          end ++ ")"
    | _ => "!nyi"
    end

  with printS (s : Stmt) : PrimString.string :=
    match s with
    | Sexpr e => printE e ++ ";"
    | Sseq ss =>
        "{
" ++ indent 2 (sepBy "
" $ printS <$> ss) ++ "
}"
    | Swhile None t s =>
        "while (" ++ printE t ++ ") " ++ printS s
    | Sdo (Sseq ss) t =>
        "do {
" ++ indent 2 (sepBy "
" $ printS <$> ss) ++ "} while (" ++ printE t ++ ");"

    | Sdecl ds =>
        sepBy "
" (printVD <$> ds)

    | _ => "nyi!"
    end

  with printVD (v : VarDecl) : PrimString.string :=
    let name_for bd :=
      match bd with
      | Bvar l _ _ => l
      | Bbind l _ _ => l
      end
    in
    match v with
    | Dvar l t None => printT t ++ " " ++ l ++ ";"
    | Dvar l t (Some e) => printT t ++ " " ++ l ++ " = " ++ printE e ++ ";"
    | Ddecompose e _ bds => "auto [" ++ sepBy ", " (name_for <$> bds) ++ "] = " ++ printE e ++ ";"
    | Dinit _ n t None => "static " ++ printT t ++ " " ++ printN n ++ ";"
    | Dinit _ n t (Some e) => "static " ++ printT t ++ " " ++ printN n ++ " = " ++ printE e ++ ";"
    end.

End with_lang.

Definition print_name (input : name) : PrimString.string :=
  printN input.

Definition TEST (nm : name) (result : PrimString.string) : Prop :=
  (print_name nm) = result.

Succeed Example _0 : TEST (Nglobal $ Nid "foo") "foo" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nop function_qualifiers.N OOPlusPlus []) "operator++()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nop function_qualifiers.N (OONew true) []) "operator new[]()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nop function_qualifiers.N (OONew false) []) "operator new()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nop function_qualifiers.N (OODelete true) []) "operator delete[]()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nop function_qualifiers.N (OODelete false) []) "operator delete()" := eq_refl.
Succeed Example _0 : TEST (Nglobal $ Nop function_qualifiers.N (OOCoawait) []) "operator coawait()" := eq_refl.

(* This seems to be the best we can do because we can not put a <<">> inside of a <<">> *)
Succeed Example _0 : (printE $ Estring (literal_string.Build_t "hello world
" 1) Tchar) = """hello world\n""" := eq_refl.
