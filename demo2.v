Require Import bedrock.lang.cpp.parser.

Local Open Scope bs_scope.

Definition bar_S :=
            (Sseq (
                (Sdecl (
                    (Dvar "t" (Tnamed "_Z1S")
                      (Some
                        (Eandclean
                          (Econstructor "_ZN1SC1EOS_" ((Xvalue,
                                (Ematerialize_temp
                                  (Econstructor "_ZN1SC1Ei" ((Prvalue, (Eint 0%Z (Tint W32 Signed))) :: nil) (Tnamed "_Z1S")))) :: nil) (Tnamed "_Z1S"))))) :: nil)) ::
                (Sexpr Prvalue
                  (Eandclean
                    (Ecall
                      (Ecast Cfunction2pointer (Lvalue,
                          (Evar (Gname "_Z3fooO1S")
                            (@Tfunction CC_C Tvoid ((Trv_ref (Tnamed "_Z1S")) :: nil)))) (Tptr
                          (@Tfunction CC_C Tvoid ((Trv_ref (Tnamed "_Z1S")) :: nil))))
                      ((Xvalue,
                          (Ematerialize_temp
                            (Emember_call
                              (inl ("_ZN1SplES_", Direct,
                                  (@Tfunction CC_C (Tnamed "_Z1S") ((Tnamed "_Z1S") :: nil)))) Lvalue
                              (Evar (Lname  "t") (Tnamed "_Z1S")) ((Prvalue,
                                  (Econstructor "_ZN1SC1ERKS_" ((Lvalue,
                                        (Ecast Cnoop (Lvalue,
                                            (Evar (Lname  "t") (Tnamed "_Z1S"))) (Qconst (Tnamed "_Z1S")))) :: nil) (Tnamed "_Z1S"))) :: nil) (Tnamed "_Z1S")))) :: nil) Tvoid))) ::
                (Sexpr Prvalue
                  (Eandclean
                    (Ecall
                      (Ecast Cfunction2pointer (Lvalue,
                          (Evar (Gname "_Z3fooO1S")
                            (@Tfunction CC_C Tvoid ((Trv_ref (Tnamed "_Z1S")) :: nil)))) (Tptr
                          (@Tfunction CC_C Tvoid ((Trv_ref (Tnamed "_Z1S")) :: nil))))
                      ((Xvalue,
                          (Ematerialize_temp
                             (Econstructor "_ZN1SC1Ei" ((Prvalue, (Eint 0%Z (Tint W32 Signed))) :: nil) (Tnamed "_Z1S")))) :: nil) Tvoid))) :: nil)).

Definition bar_int :=
            (Sseq (
                (Sdecl (
                    (Dvar "t" (Tint W32 Signed)
                      (Some (Eint 0%Z (Tint W32 Signed)))) :: nil)) ::
                (Sexpr Prvalue
                  (Ecall
                    (Ecast Cfunction2pointer (Lvalue,
                        (Evar (Gname "_Z3fooi")
                          (@Tfunction CC_C Tvoid ((Tint W32 Signed) :: nil)))) (Tptr
                        (@Tfunction CC_C Tvoid ((Tint W32 Signed) :: nil))))
                    ((Prvalue,
                        (Ebinop Badd
                          (Ecast Cl2r (Lvalue,
                              (Evar (Lname  "t") (Tint W32 Signed))) (Tint W32 Signed))
                          (Ecast Cl2r (Lvalue,
                              (Evar (Lname  "t") (Tint W32 Signed))) (Tint W32 Signed)) (Tint W32 Signed))) :: nil) Tvoid)) ::
                (Sexpr Prvalue
                  (Ecall
                    (Ecast Cfunction2pointer (Lvalue,
                        (Evar (Gname "_Z3fooi")
                          (@Tfunction CC_C Tvoid ((Tint W32 Signed) :: nil)))) (Tptr
                        (@Tfunction CC_C Tvoid ((Tint W32 Signed) :: nil))))
                    ((Prvalue,
                      (Ecast Cnoop (Prvalue, (Eint 0%Z (Tint W32 Signed))) (Tint W32 Signed))) :: nil) Tvoid)) :: nil)).

(*
Definition bar_ :=
            (Sseq (
                (Sdecl (
                    (Dvar "t"
                      (Tvar "T")
                      (Some (Eint 0%Z (Tint W32 Signed)))) :: nil)) ::
                (Sexpr Prvalue
                  (Edep_call "foo"((Prvalue,
                        (Ebinop Badd
                          (Evar (Lname  "t")
                            (Tvar "T"))
                          (Evar (Lname  "t")
                            (Tvar "T")) (Tvar "?"))) :: nil) (Tvar "?"))) ::
                (Sexpr Prvalue
                  (Edep_call "foo"((Prvalue,
                       (Eunresolved_ctor
                          (Tvar "T") ((Prvalue, (Eint 0%Z (Tint W32 Signed))) :: nil)
                          (Tvar "T"))) :: nil) (Tvar "?"))) :: nil)).
 *)

(* i don't need to pass the return values as the types
Definition bar_ :=
  fun (T T_foo1_ret T_add_ret T_foo2_ret : type) (foo_1 T_add foo_2 T_ctor1 : type -> list (ValCat * Expr) -> ValCat * Expr) =>
    (Sseq (
         (Sdecl (
              (Dvar "t"
                    T
                    (Some (Eint 0%Z (Tint W32 Signed)))) :: nil)) ::
         (let (vc,e) :=
              foo_1 T_foo1_ret [T_add T_add_ret [(Lvalue, Evar (Lname "t") T);
                                                (Lvalue, Evar (Lname "t") T)]]
          in
          Sexpr vc e) ::
         (let (vc,e) :=
              (foo_2 T_foo2_ret [T_ctor1 T [(Prvalue, (Eint 0%Z (Tint W32 Signed)))]])
          in Sexpr vc e) :: nil)).
 *)
(** TEST 1
    This is a non-dependent setup.
 *)
Module TEST1.
Definition bar_ :=
  fun (T : type) (foo_1 T_add foo_2 T_ctor1 : list (ValCat * Expr) -> (ValCat * Expr)) =>
    (Sseq (
         (Sdecl (
              (Dvar "t"
                    T
                    (Some (Eint 0%Z (Tint W32 Signed)))) :: nil)) ::
         (let (vc,e) :=
              foo_1 [T_add [(Lvalue, Evar (Lname "t") T);
                                (Lvalue, Evar (Lname "t") T)]]
          in
          Sexpr vc e) ::
         (let (vc,e) :=
              foo_2 [T_ctor1 [(Prvalue, (Eint 0%Z (Tint W32 Signed)))]]
          in Sexpr vc e) :: nil)).


Definition OOPS : (ValCat * Expr).
Proof. exact (Prvalue, Eint 0 Tvoid). Qed.

Goal exists a b c d e,
    bar_ a b c d e = bar_int.
Proof.
  rewrite /bar_ /bar_int.
  exists (Tint W32 Signed).
  eexists (fun args =>
       match args with
       | (_, e) :: nil => (Prvalue, Ecall (Ecast Cfunction2pointer _ _) [(Prvalue, e)] _)
       | _ => OOPS
       end) => /=.
  eexists (fun args =>
       match args with
       | (ve, e) :: (vf, f) :: nil =>
         (Prvalue, Ebinop Badd (Ecast Cl2r (ve, e) _) (Ecast Cl2r (vf,f) _ ) _)
       | _ => OOPS
       end) => /=.
  eexists (fun args =>
       match args with
       | (_, e) :: nil => (Prvalue, Ecall (Ecast Cfunction2pointer _ _) [(Prvalue, e)] _)
       | _ => OOPS
       end) => /=.
  eexists (fun args =>
             match args with
             | e :: nil =>
               (Prvalue, Ecast Cnoop e _)
             | _ => OOPS
             end) => /=.
  repeat f_equal.
Qed.
End TEST1.


Fixpoint nfun (n : nat) (R : Type) : Type :=
  match n with
  | 0 => R
  | S n => (ValCat * Expr) -> nfun n R
  end.

(** TEST 2
    This is a dependent setup where expressions store their *own* types
 *)
Module TEST2.
Record EXPR {n : nat} :=
  { E_type : type
  ; E_valcat : ValCat
  ; E_expr : nfun n Expr
  }.
Arguments EXPR _ : clear implicits.

Fixpoint to_pair (vc : ValCat) {n} : nfun n Expr -> nfun n (ValCat * Expr) :=
  match n as n return (nfun n Expr) -> nfun n (ValCat * Expr) with
  | 0 => fun (e : nfun 0 Expr) => (vc, e)
  | S n => fun e x => @to_pair vc n (e x)
  end.

Definition COER {n} (e : EXPR n) : nfun n (ValCat * Expr) :=
  to_pair e.(E_valcat) e.(E_expr).

Definition TEST2_bar_ :=
  fun (T : type) (foo_1 : EXPR 1) (T_add : EXPR 2) (foo_2 T_ctor1 : EXPR 1) =>
    (Sseq (
         (Sdecl (
              (Dvar "t"
                    T
                    (Some (Eint 0%Z (Tint W32 Signed)))) :: nil)) ::
         (let (vc,e) :=
              COER foo_1 (COER T_add
                               (Lvalue, Evar (Lname "t") T)
                               (Lvalue, Evar (Lname "t") T))
          in
          Sexpr vc e) ::
         (let (vc,e) :=
              COER foo_2 (COER T_ctor1 (Prvalue, (Eint 0%Z (Tint W32 Signed))))
          in Sexpr vc e) :: nil)).

End TEST2.

(** TEST 2.1
    This just extends TEST 2.
 *)
Module TEST2_1.
  Fixpoint OK (ret : type) {ls : list type} : nfun (length ls) Expr -> Prop :=
    match ls as ls return nfun (length ls) Expr -> Prop with
    | nil => fun E => type_of E = ret
    | t :: ts => fun E => forall e, type_of e.2 = t -> @OK ret ts (E e)
    end.

  Record EXPR {t : type} {ts : list type} : Type := mkExpr
  { E_valcat : ValCat ; E_expr : nfun (length ts) Expr
  ; E_type_ok : OK t E_expr
  }.
  Arguments EXPR _ _ : clear implicits.

  Fixpoint APPLY (ret : type) (ls : list type) : Type :=
    match ls as ls return Type with
    | nil => (ValCat * Expr)%type
    | t :: ts => forall e : ValCat * Expr, type_of e.2 = t -> @APPLY ret ts
    end.

  Fixpoint inst (vc : ValCat) {ret ts} : nfun (length ts) Expr -> @APPLY ret ts :=
    match ts as ts return (nfun (length ts) Expr) -> @APPLY ret ts with
    | nil => fun (e : nfun 0 Expr) => (vc, e)
    | t :: ts => fun (e : nfun (S (length ts)) Expr) x _ => @inst vc ret ts (e x)
    end.

  Definition COER {t ts} (e : EXPR t ts) : @APPLY t ts :=
    inst e.(E_valcat) e.(E_expr).

  Lemma type_of_COER_0 t (e : EXPR t []) : type_of (COER e).2 = t.
  Proof. apply e. Qed.
  Lemma type_of_COER_1 t t1 (e : EXPR t [t1]) e1 pf1 : type_of (COER e e1 pf1).2 = t.
  Proof. apply e; eauto. Qed.
  Lemma type_of_COER_2 t t1 t2 (e : EXPR t [t1;t2]) e1 pf1 e2 pf2 : type_of (COER e e1 pf1 e2 pf2).2 = t.
  Proof. apply e; eauto. Qed.

  Ltac solve_ob :=
    intros; try solve [ reflexivity | apply type_of_COER_0 | apply type_of_COER_1 | apply type_of_COER_2 ].

  Notation "'CONTEXT' e []" := (@COER _ [] e).
  Notation "'CONTEXT' e << e1 >>" := (@COER _ [_] e e1 ltac:(solve_ob)).
  Notation "'CONTEXT' e << e1 ; e2 >>" := (@COER _ [_;_] e e1 ltac:(solve_ob) e2 ltac:(solve_ob)).


  #[program] Definition bar_ :=
    fun (T Tadd Tfoo1 : type)
    (T_add : EXPR Tadd [T; T])
    (foo_1 : EXPR Tfoo1 [Tadd])
    (t : type)
    (T_ctor1 : EXPR t [Tint W32 Signed])
    (Tfoo2 : type)
    (foo_2 : EXPR Tfoo2 [t]) =>
    (Sseq (
         (Sdecl (
              (Dvar "t"
                    T
                    (Some (CONTEXT T_ctor1 << (Prvalue, Eint 0%Z (Tint W32 Signed)) >>.2))) :: nil)) ::
         (let (vc,e) :=
              CONTEXT foo_1 << CONTEXT T_add <<
                               (Lvalue, Evar (Lname "t") T) ;
                               (Lvalue, Evar (Lname "t") T) >> >>
          in
          Sexpr vc e) ::
         (let (vc,e) :=
              CONTEXT foo_2 << CONTEXT T_ctor1 << (Prvalue, (Eint 0%Z (Tint W32 Signed))) >> >>
          in Sexpr vc e) :: nil)).

  Goal exists a b c d e f g h i,
      bar_ a b c d e f g h i = bar_int.
  Proof.
    rewrite /bar_int.
    do 3 eexists _.
    eexists (@mkExpr _ [_;_] Prvalue (fun l r => Ebinop Badd (Ecast Cl2r l _) (Ecast Cl2r r _) _) _).
    eexists (@mkExpr _ [_] Prvalue (fun l => Ecall _ [l] _) _).
    eexists _.
    eexists (@mkExpr _ [_] Prvalue (fun l => l.2) _).
    eexists _.
    eexists (@mkExpr _ [_] Prvalue (fun l => Ecall _ [(_, Ecast Cnoop l _)] _) _).
    rewrite /bar_/=.
    repeat f_equal.
    Unshelve.
    all: simpl; eauto.
  Defined.

  Goal exists a b c d e f g h i,
      bar_ a b c d e f g h i = bar_S.
  Proof.
    rewrite /bar_S.
    do 3 eexists.
    eexists (@mkExpr _ [_;_] Prvalue (fun l r => Emember_call _ l.1 l.2 [(Prvalue, Econstructor _ [(_, Ecast Cnoop r _)] _)] _) _).
    eexists (@mkExpr _ [_] Prvalue (fun l => Eandclean $ Ecall _ [(Xvalue, Ematerialize_temp l.2)] _) _).
    eexists.
    eexists (@mkExpr _ [_] Prvalue (fun l => Econstructor _ [l] _) _).
    eexists.
    eexists (@mkExpr _ [_] Prvalue (fun l => Eandclean $ Ecall _ [(Xvalue, Ematerialize_temp l.2)] _) _).
    rewrite /bar_ /=.
    repeat f_equal.
    (* pre-C++17, the syntax [T x = 0] produces an elidable temporary.
       the distinction can be addressed by splitting the syntax of the initializers and
       producings 
     *)

End TEST2_1.


