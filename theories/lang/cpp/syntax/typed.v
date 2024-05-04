(*
 * Copyright (c) 2023-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.upoly.upoly.
Require bedrock.upoly.trace.
Require Import bedrock.lang.cpp.syntax.prelude.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.lang.cpp.syntax.types.
Require Import bedrock.lang.cpp.syntax.typing.
Require Import bedrock.lang.cpp.syntax.stmt.
Require Import bedrock.lang.cpp.syntax.translation_unit.

#[local] Open Scope monad_scope.

Require Import elpi.apps.locker.
Require Import bedrock.prelude.error.


Import UPoly.

(* a little "sloppy" with the errors *)
mlock Definition breadcrumb {t : Set} (_ : t) : Error.t := inhabitant.
mlock Definition Bad_allocation_function_args {lang : lang.t} (_ : list (type' lang)) : Error.t := inhabitant.
mlock Definition Can_initialize {lang : lang.t} (dt it : decltype' lang) : Error.t := inhabitant.

Module decltype.

  (**
  [to_exprtype] decomposes a declaration type into a value category
  and expression type. This is delicate because xvalue references to
  function types induce lvalue expressions.

  [to_valcat] is similar, but keeps only the value category. Matching
  on [to_valcat t] is simpler than matching on [t] when [t] might be
  an xvalue reference to a function type.
  *)
  Definition to_exprtype {lang} (t : decltype' lang) : ValCat * exprtype' lang :=
    match drop_qualifiers t with
    | Tref u => (Lvalue, u)
    | Trv_ref u =>
      match drop_qualifiers u with
      | Tfunction _ as f =>
        (**
        Both "a function call or an overloaded operator expression,
        whose return type is rvalue reference to function" and "a cast
        expression to rvalue reference to function type" are lvalue
        expressions.

        This also applies to <<__builtin_va_arg>> (an extension).

        https://en.cppreference.com/w/cpp/language/value_category#lvalue
        https://www.eel.is/c++draft/expr.call#13
        https://www.eel.is/c++draft/expr.static.cast#1
        https://www.eel.is/c++draft/expr.reinterpret.cast#1
        https://www.eel.is/c++draft/expr.cast#1 (C-style casts)

        NOTE: We return the function type without qualifiers in light
        of "A function or reference type is always cv-unqualified."
        <https://www.eel.is/c++draft/basic.type.qualifier#1>
        *)
        (Lvalue, f)
      | _ => (Xvalue, u)
      end
    | _ => (Prvalue, t)	(** Promote sharing, rather than normalize qualifiers *)
    end.
  Definition to_valcat {lang} (t : decltype' lang) : ValCat := (to_exprtype t).1.

  (**
  Compute a declaration type from a value category and expression
  type.

  Up to dropping qualifiers on reference and function types, this is
  intended to be a partial inverse of [to_exprtype].
  *)
  Definition of_exprtype {lang} (vc : ValCat) (t : exprtype' lang) : decltype' lang :=
    (**
    As [t : Mexprtype], we do not need [tref], [trv_ref].
    *)
    match vc with
    | Lvalue => Tref t
    | Xvalue => Trv_ref t
    | Prvalue => t
    end.

  Module internal.
  Section with_lang.
    Context {lang : lang.t}.
    #[local] Notation Expr := (Expr' lang).
    #[local] Notation decltype := (decltype' lang).
    #[local] Notation exprtype := (exprtype' lang).
    #[local] Notation function_type := (function_type' lang).
    #[local] Notation functype := (functype' lang).
    #[local] Notation Stmt := (Stmt' lang).

    #[local] Definition M : Set -> Set := (readerT.M (list (localname * decltype)) (trace.M Error.t)).
    #[local] Instance M_Ret : MRet M := _.
    #[local] Instance M_Ap : Ap M := _.
    #[local] Instance M_Bind : MBind M := _.
    #[local] Instance M_Fail : MFail M := _.
    #[local] Instance M_Throw : Trace Error.t M := _.
    #[local] Hint Opaque M : typeclass_instances.

    (* Bindings *)
    Record bindings : Set := { _bindings : list (localname * decltype) }.
    Instance bindings_empty : Empty bindings := {| _bindings := nil |}.
    Definition with_var {T} (x : localname) (t : decltype) : M T -> M T :=
      readerT.local (cons (x,t)).
    Definition with_bindings {T} (b : bindings) (m : M T) : M T :=
      fold_right (fun xt => with_var xt.1 xt.2) m b.(_bindings).
    #[local] Instance bindings_monoid : monoid.Monoid bindings :=
      {| monoid.monoid_unit := bindings_empty
       ; monoid.monoid_op a b := {| _bindings := a.(_bindings) ++ b.(_bindings) |} |}.
(*
    Variable lookup : name' lang -> option decltype.
    Variable locals : list (bs * type).
 *)

    Definition var_type (n : localname) : M decltype :=
      let* vars := readerT.ask in
      match List.find (fun x => bool_decide (x.1 = n)) vars with
      | None => trace (breadcrumb ("failed to find variable "%bs, n, " in "%bs, vars)) $ mfail
      | Some t => mret t.2
      end.

    (**
    The declaration type of an explicit cast to type [t] or a call to
    a function or overloaded operator returning type [t] or a
    [__builtin_va_arg] of type [t].
    *)
    Definition normalize (t : decltype) : decltype :=
      let p := to_exprtype t in
      of_exprtype p.1 p.2.

    (** Function return type *)
    Definition from_function_type (ft : function_type) : decltype :=
      normalize ft.(ft_return).
    Definition from_functype (t : functype) : M decltype :=
      match t with
      | Tfunction ft => mret $ from_function_type ft
      | _ => mfail
      end.
    Definition require_functype (t : decltype) : M function_type :=
      match t with
      | Tfunction ft => mret ft
      | _ => mfail
      end.
    Definition require_mfunctype (t : decltype) : M (decltype * function_type) :=
      match t with
      | Tmember_pointer nm ft =>
          pair (Tnamed nm) <$> require_functype ft
      | _ => mfail
      end.

    Section fixpoint.
      Context (of_expr : Expr -> M decltype).
      Context (of_stmt : Stmt -> M (option decltype)).

      Definition of_unop (op : UnOp) (t : exprtype) : M decltype :=
        match op with
        | Uminus | Uplus =>
          if is_arithmetic t then mret t else mfail (* TODO: check this *)
        | Unot => if is_arithmetic t then mret Tbool else mfail
        | Ubnot => if is_arithmetic t then mret t else mfail
        | Uunsupported _ => mfail
        end.

      Definition of_binop (op : BinOp) (l r : decltype) (t : exprtype) : M decltype :=
        match op with
        | Bdotp =>
          (**
          The value category of [e1.*e2] is (i) that of [e1] (xvalue
          or lvalue) when [e2] points to a field and (ii) prvalue when
          [e2] points to a method.

          We need only address (i) here because when [e2] is a method,
          the result of [e1.*e2] must be immediately applied, and
          cpp2v emits [Emember_call] rather than [Ebinop] for indirect
          method calls.

          https://www.eel.is/c++draft/expr.mptr.oper#6
          *)
          match l with
          | Trv_ref _ => mret $ Trv_ref t
          | _ => mret $ Tref t
          end
        | Bdotip => mret $ Tref t	(* derived from [Bdotp] *)
        | _ => mret t
        end.

      Definition of_addrof (e : Expr) : M decltype :=
        let* t := of_expr e in
        let '(vc, et) := to_exprtype t in
        let* _ := guard (vc <> Prvalue) in
        mret $ Tptr et.

      Definition of_call (f : Expr) : M decltype :=
        let* '(_, t) := to_exprtype <$> of_expr f in
        match t with
        | Tptr ft => from_functype ft
        | _ => mfail
        end.

      Definition of_member (Et : bool * exprtype) (mut : bool) (t : decltype) : M decltype :=
        let '(ref, et) := to_exprtype t in
        match ref with
        | Lvalue | Xvalue => mret $ Tref et
        | Prvalue =>
          let oty := Et.2 in
          let qual :=
            let '(ocv, _) := decompose_type oty in
            CV (if mut then false else q_const ocv) (q_volatile ocv)
          in
          let ty := tqualified qual et in
          if Et.1 then mret $ Trv_ref ty else mret $ Tref ty
        end.

      Definition of_member_call (f : MethodRef' lang) : M decltype :=
        match f with
        | inl (_, _, ft)
        | inr (Ecast Cl2r _  _ (Tmember_pointer _ ft)) => from_functype ft
        | _ => mfail
        end.

      Definition of_subscript (e1 e2 : Expr) (t : exprtype) : M decltype :=
        (**
        Neither operand ever has type [Tarray _ _] due to implicitly
        inserted array-to-pointer conversions. To compute the right
        value category, we skip over such conversions.
        *)
        let of_array (ar : Expr) : M decltype :=
          let* array_type := of_expr ar in
          match to_valcat array_type with
          | Lvalue => mret $ Tref t
          | Prvalue | Xvalue => mret $ Trv_ref t
          end
        in
        let of_base (ei : Expr) : M decltype :=
          match ei with
          | Ecast Carray2ptr ar _ _ => of_array ar
          | _ => mret $ Tref t
          end
        in
        let* t1 := of_expr e1 in
        match drop_qualifiers t1 with
        | Tptr _ => of_base e1
        | _ => of_base e2
        end.

      Definition requireL (t : decltype) : M exprtype :=
        match t with
        | Tref t => mret t
        | _ => mfail
        end.
      Definition requireGL_get (t : decltype) : M (bool * exprtype) :=
        match t with
        | Tref t => mret (false, t)
        | Trv_ref t => mret (true, t)
        | _ => mfail
        end.
      Definition requireGL (t : decltype) : M exprtype :=
        match t with
        | Tref t | Trv_ref t => mret t
        | _ => mfail
        end.
      Definition requirePR (t : decltype) : M exprtype :=
        match t with
        | Tref _ | Trv_ref _ => mfail
        | _ => mret t
        end.
      Definition requireR (t : decltype) : M exprtype :=
        match t with
        | Tref _ => mfail
        | _ => mret t
        end.
      Definition require_eq {T : Set} {_ : EqDecision T} (l : T) (r : T) : M unit :=
        trace (breadcrumb ("require equal "%bs, l, " = "%bs, r)) $
        const () <$> guard (l = r).

      (* determine if this type can be used in an <<if>> *)
      Definition require_testable (t : exprtype) : M unit :=
        match t with
        | Tnum _ _
        | Tptr _
        | Tbool
        | Tnullptr
        | Tchar_ _
        | Tfloat_ _ => mret ()
        | _ => mfail
        end.

      Definition require_ptr (t : decltype) : M exprtype :=
        match t with
        | Tptr t => mret t
        | _ => mfail
        end.

      Definition arrow_deref (arrow : bool) : decltype -> M exprtype :=
        if arrow then require_ptr else requireGL.
      Definition arrow_deref_get (arrow : bool) : decltype -> M (bool * exprtype) :=
        if arrow then fun t => pair false <$> require_ptr t else requireGL_get.


      Notation "a >=> b" := (a >>= b) (at level 61, left associativity).

      Definition can_initialize (dt : decltype) (t : decltype) : M unit :=
        trace (Can_initialize dt t) $
          let* _ := guard (drop_qualifiers dt = drop_qualifiers t) in
          mret ().

      Fixpoint check_args (ar : function_arity) (ts : list decltype) (tes : list decltype) : M unit :=
        match ts , tes with
        | nil , nil => mret ()
        | t :: ts , te :: tes =>
            (* toplevel qualifiers on arguments are ignored *)
            let* _ := can_initialize t te in
            check_args ar ts tes
        | nil , te :: tes =>
            match ar with
            | Ar_Variadic => mret () (* TODO: should check that all arguments can be passed as variadic arguments *)
            | _ => mfail
            end
        | _ , _ => mfail
        end.

      Definition of_expr_body (e : Expr) : M decltype :=
        trace (breadcrumb e) $
        let* result :=
        match e return M decltype with
        | Eparam X => mret $ Tresult_param X
        | Eunresolved_global on => mret $ Tresult_global on
        | Eunresolved_unop o e => Tresult_unop o <$> of_expr e
        | Eunresolved_binop o l r => Tresult_binop o <$> of_expr l <*> of_expr r
        | Eunresolved_call on es => Tresult_call on <$> traverse (T:=eta list) of_expr es
        | Eunresolved_member_call on obj es => Tresult_member_call on <$> of_expr obj <*> traverse (T:=eta list) of_expr es
        | Eunresolved_parenlist (Some t) es => Tresult_parenlist t <$> traverse (T:=eta list) of_expr es
        | Eunresolved_parenlist None _ => mfail
        | Eunresolved_member obj fld => Tresult_member <$> of_expr obj <*> mret fld

        | Evar ln t =>
            let* vt := var_type ln in
            let* _ := require_eq t vt in
            mret $ tref QM t
        | Eenum_const n _ => mret $ Tenum n
        | Eglobal nm ty => mret $ tref QM ty
        | Eglobal_member nm ty =>
            match nm with
            | Nscoped cls _ =>
              mret $ Tmember_pointer cls ty
            | _ => mfail
            end

        | Echar _ t =>
            match t with
            | Tchar_ _
            | Tuchar | Tschar => mret t
            | _ => mfail
            end
        | Estring chars t =>
            mret $ Tref $ Tarray (Qconst t) (1 + list_numbers.lengthN chars)
        | Eint _ t =>
            let* _ := guard (t ∈ [Tchar;Tuchar;Tschar;Tshort;Tushort;Tint;Tuint;Tlong;Tulong;Tlonglong;Tulonglong]) in
            mret t
        | Ebool _ => mret Tbool
        | Eunop op e t =>
            let* et := of_expr e >>= requirePR in
            let* t' := of_unop op et >>= requirePR in
            let* _ := guard (t = t') in
            mret t
        | Ebinop op l r t =>
            let* lt := of_expr l in
            let* rt := of_expr r in
            of_binop op lt rt t
        | Ederef e t =>
            let* t' := of_expr e >>= require_ptr in
            let* _ := guard (t = t') in
            mret $ Tref t
        | Eaddrof e =>
            let* t := of_expr e >>= requireGL in
            mret $ Tptr t
        | Eassign le re t =>
            let* lt := of_expr le >>= requireL in
            let* rt := of_expr re >>= requireR in
            let* _ := guard (lt = rt) in
            let* _ := guard (lt = t) in
            mret $ Tref lt
        | Eassign_op op le re t =>
            (* TODO: i still need to check that the operation is permitted at this type *)
            let* lt := of_expr le >>= requireL in
            let* rt := of_expr re >>= requireR in
            let* _ := guard (lt = rt) in
            let* _ := guard (lt = t) in
            mret $ Tref lt
        | Epreinc e t
        | Epredec e t =>
            (* TODO: <<+>>or <<->> must be valid *)
            let* lt := of_expr e >>= requireL in
            let* _ := guard (lt = t) in
            mret $ Tref lt
        | Epostinc e t
        | Epostdec e t =>
            (* TODO: <<+>>or <<->> must be valid *)
            let* lt := of_expr e >>= requireL in
            let* _ := guard (lt = t) in
            mret lt

        | Eseqand le re
        | Eseqor le re =>
            let* _ := of_expr le >>= require_testable in
            let* _ := of_expr re >>= require_testable in
            mret Tbool
        | Ecomma e1 e2 =>
            let* _ := of_expr e1 in
            of_expr e2
        | Ecall f es =>
            let* ft := of_expr f >=> require_ptr >=> require_functype in
            let* ts := traverse (T:=eta list) of_expr es in
            let* _ := check_args ft.(ft_arity) ft.(ft_params) ts in
            mret ft.(ft_return)
        | Ecast Cl2r e vc et =>
            let* t := of_expr e >=> requireGL in
            let* _ := guard (vc = Prvalue) in
            let* _ := guard (drop_qualifiers t = et) in
            mret $ of_exprtype vc et
        | Ecast _ e vc et =>
            let* _ := of_expr e in
            mret $ of_exprtype vc et
        | Emember arrow e _ mut t =>
            let* edt := of_expr e >>= arrow_deref_get arrow in
            of_member edt mut t
        | Emember_call arrow f obj es =>
            let* objT := of_expr obj >>= arrow_deref arrow in
            let* tes := traverse (T:=eta list) of_expr es in
            let* ft :=
              match f with
              | inl (_, _, ft) => require_functype ft
              | inr e =>
                  let* ft := of_expr e in
                  match ft with
                  | Tmember_pointer cls (Tfunction ft) =>
                      mret ft
                  | _ => mfail
                  end
              end
            in
            let* _ := check_args ft.(ft_arity) ft.(ft_params) tes in
            mret ft.(ft_return)

        | Eoperator_call _ f es =>
            let* tes := traverse (T:=eta list) of_expr es in
            let* '(result, fargs) :=
              match f with
              | operator_impl.Func _ ft =>
                  let* ft := require_functype ft in
                  mret (ft.(ft_return), ft.(ft_params))
              | operator_impl.MFunc _ _ ft =>
                  (* TODO: the type of the member function does not currently
                     contain the [Tmember_pointer] type *)
                  let* objT :=
                    match tes with
                    | obj :: _ => mret [obj]
                    | _ => mret []
                    end
                  in
                  let* ft := require_functype ft in
                  mret (ft.(ft_return), objT ++ ft.(ft_params))
              end
            in
            let* _ := check_args Ar_Definite fargs tes in
            mret result
        | Esubscript e1 e2 t => of_subscript e1 e2 t
        | Esizeof te t
        | Ealignof te t =>
            let* _ :=
              match te with
              | inl t => mret ()
              | inr e => const () <$> of_expr e
              end
            in
            const Tsize_t <$> guard (t = Tsize_t)
        | Eoffsetof _ _ t => mret t
        | Econstructor f es t =>
            (* TODO: check the type of the constructor [f] *)
            let* tes := traverse (T:=eta list) of_expr es in
            mret t
        | Eimplicit e => of_expr e
        | Eimplicit_init t =>
            (**
          "References cannot be value-initialized".

          https://en.cppreference.com/w/cpp/language/value_initialization
             *)

            let* _ := requirePR t in
            mret t
        | Eif tst thn els vc t =>
            let rt :=
              match vc with
              | Prvalue => t
              | Lvalue => Tref t
              | Xvalue => Trv_ref t
              end
            in
            let* _ := of_expr tst >>= require_testable in
            let* tthn := of_expr thn >>= require_eq rt in
            let* tels := of_expr els >>= require_eq rt in
            mret rt
        | Eif2 x lete tst thn els vc t =>
            let* lt := of_expr lete in
            with_var (localname.anon x) lt $
              let* _ := of_expr tst >>= require_testable in
              let* tthn := of_expr thn in
              let* _ := of_expr els >>= require_eq tthn in
              let* _ := guard (of_exprtype vc t = tthn) in
              mret $ of_exprtype vc t
        | Ethis t => mret t
        | Enull => mret Tnullptr
        | Einitlist es oe t =>
            let* _ := traverse (T:=eta list) of_expr es in
            let* _ :=
              match oe with
              | None => mret tt
              | Some e => const tt <$> of_expr e
              end
            in
            mret t
        | Enew (alloc, alloc_ty) aes nf aty osz oinit =>
            let* ats := traverse (T:=eta list) of_expr aes in
            let* afty := require_functype alloc_ty in
            let* _ :=
              let* _ := guard (afty.(ft_return) = Tptr Tvoid) in
              let* params :=
                match afty.(ft_params) return M (list decltype) with
                | Tsize_t :: params => mret params
                | args => trace (Bad_allocation_function_args args) $ mfail
                end
              in
              let* params :=
                if nf is new_form.Allocating true then
                  match params with
                  | Talign_t :: params => mret params
                  | _ => trace (Bad_allocation_function_args afty.(ft_params)) mfail
                  end
                else
                  mret params
              in
              check_args afty.(ft_arity) params ats
            in
            let* _ :=
              match osz with
              | None => mret tt
              | Some sz =>
                  let* tsz := of_expr sz in
                  if is_arithmetic tsz then mret tt else mfail
              end
            in
            let* _ :=
              match oinit with
              | None => mret tt
              | Some init => let* _ := of_expr init in mret tt (* TODO: check result type against [aty] *)
              end
            in
            mret $ Tptr aty
        | Edelete _ (del, del_ty) e ty =>
            let* et := of_expr e >>= require_ptr in
            let* _ := guard (ty = et) in (* TODO: constness check? *)
            mret Tvoid
        | Eandclean e => of_expr e
        | Ematerialize_temp e vc =>
            let* _ := guard (vc <> Prvalue) in
            of_exprtype vc <$> (of_expr e >>= requirePR)
        | Eatomic _ es t =>
            let* tes := traverse (T:=eta list) of_expr es in
            mret t
        | Estmt s t =>
            let* st := of_stmt s in
            let* _ := require_eq st (Some t) in
            mret t
        | Eva_arg _ t => mret $ normalize t
        | Epseudo_destructor _ _ _ => mret Tvoid
        | Earrayloop_init n e level _ e2 t =>
            let* _ := of_expr e in
            let* _ :=
              with_var (localname.arrayloop_index level) Tsize_t $
                       with_var (localname.opaque n) t $
                of_expr e2 in
            mret t
        | Earrayloop_index n t =>
            let* _ := var_type (localname.arrayloop_index n) >>= require_eq t in
            mret t (* always pr-values? *)
        | Eopaque_ref n vc t =>
            let* vt := var_type (localname.opaque n) in
            let* _ := can_initialize vt t in
            (* ^^ in practice, the type and the recorded variable type
               differ by <<const>> qualifiers in instance-specific ways *)
            mret $ of_exprtype vc t
        | Eunsupported _ vc t => mret $ of_exprtype vc t
        end
        in
        let* _ :=
          let shallow := decltype_of_expr e in
          trace (breadcrumb ("type mismatch"%bs, result, shallow)) $ require_eq result shallow
        in
        mret result.
    End fixpoint.

    Definition big_op `{Mon : monoid.Monoid m} `{Traverse T} (ls : T m) : m :=
      writer.value $ traverse (F:=writer.M m) (T:=T) (writer.tell) ls.

    Section var_decl.
      Context (of_expr : Expr -> M decltype).

      Fixpoint check_decl (d : VarDecl' lang) : M bindings :=
        trace (breadcrumb d)
        match d with
        | Dvar lname ty oinit =>
            let* _ :=
              match oinit with
              | None => mret tt
              | Some init =>
                  let* _ := with_var lname ty $ of_expr init >>= can_initialize ty in
                  mret tt
              end
            in
            mret ({| _bindings := [(lname, ty)] |})
        | Ddecompose e v ds =>
            (* TODO: this is wrong, it requires a more subtle binding form because [e] is bound during the
              evaluation of the declarations, but is unbound afterwards *)
            let* t := of_expr e in
            let* (bindings : list bindings) := with_var v t $ traverse (T:=eta list) check_decl ds in
            mret $ big_op bindings
        | Dinit _ nm ty oinit =>
            let* _ :=
              match oinit with
              | None => mret tt
              | Some init =>
                  let* _ := of_expr init >>= can_initialize ty in
                  mret tt
              end
            in
            mret monoid.monoid_unit
        end.

    End var_decl.

    Section stmt.
      Context (of_expr : Expr -> M decltype).

      Notation check_decl := (check_decl of_expr) (only parsing).

      Definition check_decls (ds : list (VarDecl' lang)) : M bindings :=
        big_op (T:=eta list) <$> traverse (F:=M) (T:=eta list) check_decl ds.

      Fixpoint check_stmt_body (s : Stmt' lang) : M (bindings * option decltype) :=
        let check_stmt := check_stmt_body in
        trace (breadcrumb s)
        match s with
        | Sgoto _ => mret (∅, None)
        | Slabeled _ s => check_stmt s
        | Sexpr e =>
            pair monoid.monoid_unit ∘ Some <$> of_expr e
        | Sdefault | Scase _ | Sbreak | Scontinue => mret (∅, None)
        | Sseq ss =>
            (fix block ss :=
               match ss with
               | nil => mret (∅, None)
               | s :: ss =>
                   let* '(b,d) := check_stmt s in
                   with_bindings b $ block ss
               end) ss
        | Sif vd tst thn els =>
            let* ds := from_option check_decl (mret monoid.monoid_unit) vd in
            let* _ :=
              with_bindings ds $
                let* _ := of_expr tst >>= require_testable in
                let* _ := check_stmt thn in
                check_stmt els
            in mret (∅, None)
        | Sswitch vd tst b =>
            let* ds := from_option check_decl (mret monoid.monoid_unit) vd in
            let _ :=
              with_bindings ds $
                let* _ := of_expr tst >>= require_eq Tint in (* TODO: BAD *)
                check_stmt b
            in mret (∅, None)
        | Swhile vd tst body =>
            let* ds := from_option check_decl (mret monoid.monoid_unit) vd in
            let k :=
              with_bindings ds $
                let* _ := of_expr tst >>= require_testable in
                check_stmt body
            in mret (∅, None)
        | Sdo s tst =>
            let* _ := check_stmt s in
            let* _ := of_expr tst >>= require_testable in (* TODO *)
            mret (∅, None)
        | Sfor vd otst oincr body =>
            let* '(ds, _) := from_option check_stmt (mret (monoid.monoid_unit, None)) vd in
            let* _ :=
              with_bindings ds $
                let* _ := from_option (fun e => of_expr e >>= require_testable) (mret tt) $ otst in
                let* _ := from_option (fun e => let* _ := of_expr e in mret tt) (mret tt) $ oincr in
                check_stmt body
            in mret (∅, None)
        | Sdecl ds =>
            let* b := check_decls ds in
            mret (b, None)
        | Sreturn None => mret (∅, None)
        | Sreturn (Some e) =>
            let* _ := of_expr e in
            mret (∅, None)
        | Sattr _ s =>
            check_stmt s (* TODO: confirm scope *)
        | Sasm _ _ ins outs args =>
            let* _ := traverse (T:=eta list) (fun ab => of_expr ab.2) ins in
            let* _ := traverse (T:=eta list) (fun ab => of_expr ab.2) outs in
            mret (∅, None)
        | Sunsupported _ => mfail
        end.
    End stmt.

    Fixpoint of_expr (e : Expr) : M decltype :=
      of_expr_body of_expr check_stmt e
    with check_stmt (s : Stmt) : M (option decltype) :=
      snd <$> check_stmt_body of_expr s.


    Definition Merr : Set -> Set := trace.M Error.t.

    Definition check_func (f : Func' lang) : Merr unit :=
      match f.(f_body) with
      | None => mret ()
      | Some (Impl body) =>
          const () <$> readerT.run (with_bindings {| _bindings := f.(f_params) |} $ check_stmt body) []
      | Some (Builtin _) => mret ()
      end.

    Definition check_method (m : Method' lang) : Merr unit :=
      match m.(m_body) with
      | Some (UserDefined s) =>
          const () <$> readerT.run (with_bindings {| _bindings := m.(m_params) |} $ check_stmt s) []
      | _ => mret ()
      end.

    Definition check_ctor (c : Ctor' lang) : Merr unit :=
      match c.(c_body) with
      | Some (UserDefined (inits, body)) =>
          readerT.run (with_bindings {| _bindings := c.(c_params) |} $
                         let* _ := traverse (T:=eta list) (fun init => of_expr init.(init_init)) inits in
                         const () <$> check_stmt body) []
      | _ => mret ()
      end.

    Definition check_dtor (d : Dtor' lang) : Merr unit :=
      match d.(d_body) with
      | Some (UserDefined body) =>
          readerT.run (const () <$> check_stmt body) []
      | _ => mret ()
      end.

    Definition check_obj_value (o : ObjValue' lang) : Merr unit :=
      trace (breadcrumb o)
      match o with
      | Ovar _ oinit =>
          match oinit with
          | None => mret tt
          | Some init =>
              const () <$> readerT.run (of_expr init) []
          end
      | Ofunction f => check_func f
      | Omethod m => check_method m
      | Oconstructor c => check_ctor c
      | Odestructor d => check_dtor d
      end.

  End with_lang.

  End internal.

  Definition of_expr {lang} (tu : translation_unit) (e : Expr' lang) : trace.M Error.t (decltype' lang) :=
    let lookup :=
      match lang as lang return _ with
      | lang.cpp => fun nm => fmap (M:=fun t => option t) type_of_value $ tu.(symbols) !! nm
      | lang.temp => fun _ => None
      end
    in
    readerT.run (internal.of_expr e) [].

  Definition check_tu (tu : translation_unit) : trace.M Error.t unit :=
    let fn (nm_v : name * ObjValue) :=
      trace (breadcrumb nm_v.1) $ internal.check_obj_value nm_v.2
    in
    let* _ := traverse (T:=eta list) fn $ compare.NM.elements tu.(symbols) in
    mret tt.
End decltype.

Module exprtype.
Section exprtype.
  Context {lang : lang.t} (tu : translation_unit).

  Definition of_expr (e : Expr' lang) : option (ValCat * exprtype' lang) :=
    trace.runO $ decltype.to_exprtype <$> decltype.of_expr tu e.

  Definition of_expr_drop (e : Expr' lang) : option (exprtype' lang) :=
    trace.runO $ drop_reference <$> decltype.of_expr tu e.

  Definition of_expr_check (P : ValCat -> Prop) `{!∀ vc, Decision (P vc)}
      (e : Expr' lang) : option (exprtype' lang) :=
    of_expr e >>= fun p => guard (P p.1) ;; mret p.2.

End exprtype.
End exprtype.

(*
(**
Convenience functions
*)
Section convenience.
  Context {lang : lang.t} (tu : translation_unit).

  Definition decltype_of_expr (e : Expr' lang) : decltype' lang :=
    default (Tunsupported "decltype_of_expr: cannot determine declaration type") $
    decltype.of_expr tu e.
  Definition exprtype_of_expr (e : Expr' lang) : ValCat * exprtype' lang :=
    decltype.to_exprtype $ decltype_of_expr e.
  Definition valcat_of (e : Expr' lang) : ValCat := (exprtype_of_expr e).1.
  Definition type_of (e : Expr' lang) : exprtype' lang := (exprtype_of_expr e).2.
End convenience.
*)


(**
Module exprtype.

  Section fixpoint.
    #[local] Notation traverse_list := mapM.

    Definition to_decltype (vc_t : ValCat * exprtype) : decltype :=
      match vc_t.1 with
      | Lvalue => Tref vc_t.2
      | Xvalue => Trv_ref vc_t.2
      | Prvalue => vc_t.2
      end.

    Definition requireL (vc_t : ValCat * exprtype) : M exprtype :=
      match vc_t.1 with
      | Lvalue => mret vc_t.2
      | _ => mfail
      end.
    Definition requireGL (vc_t : ValCat * exprtype) : M exprtype :=
      match vc_t.1 with
      | Lvalue | Xvalue => mret vc_t.2
      | _ => mfail
      end.

    Fixpoint of_expr (e : Expr) : M (ValCat * exprtype) :=

        match e return M decltype with
        | Eparam X => mret (Prvalue, Tresult_param X)
        | Eunresolved_global on => mret (Prvalue, Tresult_global on)
        | Eunresolved_unop o e => pair Prvalue ∘ Tresult_unop o <$> to_decltype (of_expr e)
        | Eunresolved_binop o l r => Tresult_binop o <$> of_expr l <*> of_expr r
        | Eunresolved_call on es => Tresult_call on <$> traverse_list of_expr es
        | Eunresolved_member_call on obj es => Tresult_member_call on <$> of_expr obj <*> traverse_list of_expr es
        | Eunresolved_parenlist (Some t) es => Tresult_parenlist t <$> traverse_list of_expr es
        | Eunresolved_parenlist None _ => mfail
        | Eunresolved_member obj fld => Tresult_member <$> of_expr obj <*> mret fld

        | Evar _ t => mret $ tref QM t
        | Eenum_const n _ => mret $ Tenum n
        | Eglobal nm ty => mret ty (* TODO *)

        | Echar _ t => mret t
        | Estring chars t =>
            mret $ Tref $ Tarray (Qconst t) (1 + list_numbers.lengthN chars)
        | Eint _ t => mret t
        | Ebool _ => mret Tbool
        | Eunop _ _ t => mret t
        | Ebinop op le re t => of_binop op l t
        | Ederef e t =>
            let* et := of_expr e in
            match et with
            | Tptr t' =>
                let* _ := guard (t = t') in
                mret $ Tref t
            | _ => mfail
            end
        | Eaddrof e => of_addrof e
        | Eassign le re t =>
            let* lt := of_expr le in
            let* _ := valcat_of le >>= fun vc => guard (vc = Lvalue) in
            let* rt := of_expr re in
            _
        | Eassign_op _ _ _ t
        | Epreinc _ t => mret $ Tref t
        | Epostinc _ t => mret t
        | Epredec _ t => mret $ Tref t
        | Epostdec _ t => mret t
        | Eseqand _ _
        | Eseqor _ _ => mret Tbool
        | Ecomma _ e2 => of_expr e2
        | Ecall f _ => of_call f
        | Ecast _ _ vc et => mret $ of_exprtype vc et
        | Emember e _ mut t => of_member e mut t
        | Emember_call f _ _ => of_member_call f
        | Eoperator_call _ f _ => from_operator_impl f
        | Esubscript e1 e2 t => of_subscript e1 e2 t
        | Esizeof _ t
        | Ealignof _ t
        | Eoffsetof _ _ t
        | Econstructor _ _ t => mret t
        | Eimplicit e => of_expr e
        | Eimplicit_init t =>
          (**
          "References cannot be value-initialized".

          https://en.cppreference.com/w/cpp/language/value_initialization
          *)
          mret t
        | Eif _ _ _ vc t
        | Eif2 _ _ _ _ _ vc t => mret $ of_exprtype vc t
        | Ethis t => mret t
        | Enull => mret Tnullptr
        | Einitlist _ _ t => mret t
        | Enew _ _ _ aty _ _ => mret $ Tptr aty
        | Edelete _ _ _ _ => mret Tvoid
        | Eandclean e => of_expr e
        | Ematerialize_temp e vc => of_materialize_temp e vc
        | Eatomic _ _ t => mret t
        | Eva_arg _ t => mret $ normalize t
        | Epseudo_destructor _ _ _ => mret Tvoid
        | Earrayloop_init _ _ _ _ _ t
        | Earrayloop_index _ t => mret t
        | Eopaque_ref _ vc t
        | Eunsupported _ vc t => mret $ of_exprtype vc t
        end
**)
