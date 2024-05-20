(*
 * Copyright (C) BedRock Systems Inc. 2023-2024
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import stdpp.prelude.
Require Import bedrock.prelude.base.
Require Import bedrock.prelude.bytestring.
Require Import bedrock.upoly.upoly.
Require Import bedrock.upoly.option.
Require Import bedrock.prelude.parsec.
Require Import bedrock.lang.cpp.syntax.

(** ** A parser for C++ names.

    This does not currently support all of C++ names, e.g. those
    that contain expressions. In general, it may be difficult to support
    some expressions.
 *)

Definition ident_char (b : Byte.byte) : bool :=
  let n := Byte.to_N b in
  bool_decide ((Reduce (Byte.to_N "a") ≤ n ≤ Reduce (Byte.to_N "z")) \/
               (Reduce (Byte.to_N "A") ≤ n ≤ Reduce (Byte.to_N "Z")) \/
               b = "_"%byte)%N.


Module parser.
  Import parsec.
  Import UPoly.

  #[local] Open Scope monad_scope.

  #[local] Definition M := (parsec.M (eta option)).

  #[local] Instance M_ret : MRet M := _.
  #[local] Instance M_map : FMap M := _.
  #[local] Instance M_ap : Ap M := _.
  #[local] Instance M_bind : MBind M := _.
  #[local] Instance M_alt : Alternative M := _.

  Definition run {T} (m : M T) (str : bs) : option (bs * T) :=
    match parsec.run m str with
    | Some (Datatypes.Some (rest, result)) => Some (rest, result)
    | _ => None
    end.

  Definition run_full {T} (p : M T) (str : bs) : option T :=
    let m : M T := (fun x _ => x) <$> p <*> eos in
    fmap (M:=eta option) (fun '(_,b) => b) $ run m str.

  Definition ident : M bs :=
    let* f := char ident_char in
    (fun xs => BS.String f $ BS.parse xs) <$> star (char ident_char <|> digit).

  Definition token (b : bs) : M unit :=
    ignore_ws (exact b).

  Definition NEXT {T} (n : nat) (f : nat -> M T) : M T :=
    match n with
    | 0 => mfail
    | S n => f n
    end.

  Section with_lang.
    Context {lang : lang.t}.
    Notation type := (type' lang).
    Notation name := (name' lang).

    Fixpoint parse_postfix_type (t : type) (fuel : nat) : M type :=
      let* _ := ws in
      let* '(continue, upd) :=
        (let* _ := exact "&&" in mret (true, Trv_ref)) <|>
          (let* _ := exact "&" in mret (true, Tref)) <|>
          (let* _ := exact "*" in mret (true, Tptr)) <|>
          (let* _ := exact "const" in mret (true, fun x => Qconst x)) <|>
          (let* _ := exact "volatile" in mret (true, fun x => Qvolatile x)) <|>
          (mret (false, fun x => x))
      in
      if (continue : bool) then
        NEXT fuel (parse_postfix_type (upd t))
      else mret t.

    Definition basic_types : list (list bs * type) :=
      let s_or_u_l (b : list bs) (s u : type) :=
        [(b, s); ("signed" :: b, s); ("unsigned" :: b, u)]%bs
      in
      let s_or_u b := s_or_u_l [b] in
      [ (["bool"], Tbool)
      ; (["void"], Tvoid)
      ; (["nullptr_t"], Tnullptr)
      ; (["float16"], Tfloat16)
      ; (["float128"], Tfloat128)
      ; (["float"], Tfloat)
      ; (["double"], Tdouble)
      ; (["long"; "double"], Tlongdouble)
      ; (["char"], Tchar)
      ; (["unsigned"; "char"], Tuchar)
      ; (["signed"; "char"], Tschar) ]%bs ++
      s_or_u "short"%bs Tshort Tushort ++
      s_or_u "int"%bs Tint Tuint ++
      s_or_u_l ["long";"long"]%bs Tlonglong Tulonglong ++
      s_or_u "long"%bs Tlong Tulong ++
      [ (["unsigned"], Tuint)
      ; (["signed"], Tint) ]%bs.

    Definition basic_type : M type :=
      anyOf $ (fun '(tkns, val) => (fun _ => val) <$> (seqs $ token <$> tkns)) <$> basic_types.

    Definition operators : list (bs * OverloadableOperator) :=
      (* this is used in an early commit manner, so longer operators
         need to come first
         TODO: list is incomplete
       *)
      [ ("~", OOTilde)
      ; ("!", OOExclaim)
      ; ("++", OOPlusPlus)
      ; ("--", OOMinusMinus)
      ; ("&&", OOAmpAmp)
      ; ("&", OOAmp)
      ; ("||", OOPipePipe)
      ; ("==", OOEqualEqual)
      ; ("<=", OOLessEqual)
      ; ("<<", OOLessLess)
      ; (">=", OOGreaterEqual)
      ; (">>", OOGreaterGreater)
      ; ("&=", OOAmpEqual)
      ; ("|=", OOPipeEqual)
      ; ("<<=", OOLessLessEqual)
      ; (">>=", OOGreaterGreaterEqual)
      ; ("->*", OOArrowStar)
      ; ("->", OOArrow)
      ; ("<", OOLess)
      ; ("[]", OOSubscript)
      ; ("new[]", OONew true)
      ; ("delete[]", OODelete true)
      ; ("new", OONew false)
      ; ("delete", OODelete false)
      ; ("*", OOStar)
      ; ("+", OOPlus)
      ; ("-", OOMinus)
      ; ("/", OOSlash)
      ; ("%", OOPercent)
      ; ("^", OOCaret)
      ; ("|", OOPipe)
      ]%bs.

    Fixpoint firstOf {T} (ls : list (M T)) : M T :=
      match ls with
      | nil => mfail
      | l :: ls =>
          let* x := optional l in
          match x with
          | None => firstOf ls
          | Some x => mret x
          end
      end.

    Definition operator : M OverloadableOperator :=
      firstOf $ (fun '(lex, syn) => const syn <$> token lex) <$> operators.

    (** classification of names based to account for destructors and overloadable
        operators. *)
    Variant name_type : Set :=
      | Simple (_ : bs)
      | Dtor (_ : bs)
      | Op (_ : OverloadableOperator).

    (* The core parsers are based on fuel to handle the mutual recursion *)
    Fixpoint parse_type (fuel : nat) : M type :=
      let* quals :=
        star (((fun _ => Qconst (lang:=lang)) <$> token "const") <|>
              ((fun _ => Qvolatile) <$> token "volatile"))
      in
      let* t :=
        basic_type <|>
        ((fun _ => Tparam) <$> exact "$" <*> ident) <|>
        (Tnamed <$> NEXT fuel parse_name)
      in parse_postfix_type (List.fold_right (fun f x => f x) t quals) fuel

    with parse_name (fuel : nat) : M name :=
      let* (x : list (atomic_name' _ * _)) :=
        sepBy (exact "::") (NEXT fuel parse_name_component)
      in
      match x with
      | nil => mfail (* unreachable *)
      | (nm, oinst) :: xs =>
          let sp oi :=
            match oi with
            | None => fun x => x
            | Some (_, i) => fun x => Ninst x i
            end
          in
          let* root :=
            (mret $ Nglobal nm)
          in
          mret (List.fold_left (fun '(acc, last) '(nm, oinst) =>
                                  match nm with
                                  | Nfunction [] (Nf fnm) args =>
                                      if bool_decide (Nid fnm = last) then
                                        (sp oinst (Nscoped acc $ Nfunction [] Nctor args), nm)
                                      else
                                        (sp oinst (Nscoped acc nm), nm)
                                  | _ =>
                                      (sp oinst (Nscoped acc nm), nm)
                                  end) xs
            (root, nm)).1
      end

    (* name components basically amount to atomic names with an optional template
       specialization after them. They are complex because function names include their
       arguments.
     *)
    with parse_name_component (fuel : nat) : M (atomic_name' lang * option (list bs * list (temp_arg' _))) :=
      let* (nm : name_type) :=
        let* op := optional (token "operator") in
        match op with
        | None => let* d := optional (token "~") in
                 match d with
                 | None => Simple <$> ident
                 | Some _ => Dtor <$> ident
                 end
        | Some _ => Op <$> operator
        end
      in
      let mk_atomic_name (nm : name_type) (args : option _) : M (atomic_name' _) :=
        match args with
        | None => match nm with
                 | Simple nm => mret $ Nid nm
                 | Dtor _ => mfail
                 | Op _ => mfail
                 end
        | Some (args, quals) =>
            mret $ Nfunction quals (match nm with
                                    | Dtor _ => Ndtor
                                    | Simple nm => Nf nm
                                    | Op oo => Nop oo
                                    end) args
        end
      in
      let parse_args : M _ :=
        optional (let* args := quoted (token "(") (token ")") $
                    sepBy (token ",") (NEXT fuel parse_type) in
                  let* quals := star (anyOf $ [const Nconst <$> token "const";
                                               const Nvolatile <$> token "volatile";
                                               const Nrvalue <$> token "&&";
                                               const Nlvalue <$> token "&"]) in
                  mret (args, quals))
      in
      let* x := optional (quoted (token "<") (token ">") $ sepBy (token ",") (NEXT fuel parse_type)) in
      let* nm := let* a := parse_args in mk_atomic_name nm a in
      match x with
      | None => mret (nm, None)
      | Some bs =>
          mret (nm, Some ([], Atype <$> bs))
      end.
  End with_lang.

End parser.

Definition parse_name (input : list Byte.byte) : option name :=
  parser.run_full (parser.parse_name 1000) $ BS.parse input.
