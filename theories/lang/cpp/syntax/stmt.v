(*
 * Copyright (c) 2020-2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
From bedrock.lang.cpp.syntax Require Import names types expr.
Require Import bedrock.prelude.bytestring.

Set Primitive Projections.

Variant SwitchBranch : Set :=
| Exact (_ : Z)
| Range (_ _ : Z).
#[global] Instance: EqDecision SwitchBranch.
Proof. solve_decision. Defined.

Inductive VarDecl : Set :=
| Dvar (name : localname) (_ : type) (init : option Expr)
| Ddecompose (_ : Expr) (anon_var : ident) (_ : list VarDecl)
  (* initialization of a function-local [static]. See https://eel.is/c++draft/stmt.dcl#3 *)
| Dinit (thread_safe : bool) (name : obj_name) (_ : type) (init : option Expr).
#[global] Instance: EqDecision VarDecl.
Proof.
  refine (fix dec (x y : VarDecl) : {x = y} + {x <> y} :=
            match x as x , y as y return {x = y} + {x <> y} with
            | Ddecompose xi xx xs , Ddecompose yi yx ys =>
              match List.list_eq_dec dec xs ys with
              | left pf => match decide (xi = yi /\ xx = yx) with
                          | left pf' => left _
                          | right pf' => right _
                          end
              | right pf => right _
              end
            | Dvar x tx ix , Dvar y ty iy =>
              match decide (x = y /\ tx = ty /\ ix = iy) with
              | left pf => left _
              | right pf => right _
              end
            | Dinit xts x tx ix , Dinit yts y ty iy =>
              match decide (xts = yts /\ x = y /\ tx = ty /\ ix = iy) with
              | left pf => left _
              | right pf => right _
              end
            | _ , _ => right _
            end); try solve [ intro pf; inversion pf ].
  { destruct pf as [ ? [ ? ? ] ].
    subst; reflexivity. }
  { intro X; inversion X; apply pf; tauto. }
  { destruct pf' as [ ? ? ]; f_equal; assumption. }
  { intro zz; inversion zz; apply pf'; tauto. }
  { intro. apply pf. inversion H; auto. }
  { by destruct pf as [ -> [ -> [ -> -> ] ] ]. }
  { intro. apply pf. inversion H; tauto. }
Defined.

#[global] Instance VarDecl_is_dependent : IsDependent VarDecl :=
  fix go decl :=
  let _ : IsDependent _ := go in
  match decl with
  | Dvar _ t init => is_dependent t || is_dependent init
  | Ddecompose e _ decls => is_dependent e || is_dependent decls
  | Dinit _ _ t init => is_dependent t || is_dependent init
  end.

Inductive Stmt : Set :=
| Sseq    (_ : list Stmt)
| Sdecl   (_ : list VarDecl)

| Sif     (_ : option VarDecl) (_ : Expr) (_ _ : Stmt)
| Swhile  (_ : option VarDecl) (_ : Expr) (_ : Stmt)
| Sfor    (_ : option Stmt) (_ : option Expr) (_ : option Expr) (_ : Stmt)
| Sdo     (_ : Stmt) (_ : Expr)

| Sswitch (_ : option VarDecl) (_ : Expr) (_ : Stmt)
| Scase   (_ : SwitchBranch)
| Sdefault

| Sbreak
| Scontinue

| Sreturn (_ : option Expr)

| Sexpr   (_ : Expr)

| Sattr (_ : list ident) (_ : Stmt)

| Sasm (_ : bs) (volatile : bool)
       (inputs : list (ident * Expr))
       (outputs : list (ident * Expr))
       (clobbers : list ident)

| Slabeled (_ : ident) (_ : Stmt)
| Sgoto (_ : ident)
| Sunsupported (_ : bs).
#[global] Instance Stmt_eq_dec : EqDecision Stmt.
Proof.
  rewrite /RelDecision /Decision.
  fix IHs 1.
  rewrite -{1}/(EqDecision Stmt) in IHs.
  decide equality; try solve_trivial_decision.
Defined.

#[global] Instance Stmt_is_dependent : IsDependent Stmt :=
  fix go s :=
  let _ : IsDependent _ := go in
  match s with
  | Sseq ss => is_dependent ss
  | Sdecl ds => is_dependent ds
  | Sif d e s1 s2 => is_dependent d || is_dependent e || is_dependent s1 || is_dependent s2
  | Swhile d e s => is_dependent d || is_dependent e || is_dependent s
  | Sfor s1 e1 e2 s2 => is_dependent s1 || is_dependent e1 || is_dependent e2 || is_dependent s2
  | Sdo s e => is_dependent s || is_dependent e
  | Sswitch d e s => is_dependent d || is_dependent e || is_dependent s
  | Scase _
  | Sdefault
  | Sbreak
  | Scontinue => false
  | Sreturn m => is_dependent m
  | Sexpr e => is_dependent e
  | Sattr _ s => is_dependent s
  | Sasm _ _ inputs outputs _ => is_dependent (inputs.*2) || is_dependent (outputs.*2)
  | Slabeled _ s => is_dependent s
  | Sgoto _
  | Sunsupported _ => false
  end.

Definition Sskip := Sseq nil.

Variant OrDefault {t : Set} : Set :=
| Defaulted
| UserDefined (_ : t).
Arguments OrDefault : clear implicits.

#[global] Instance OrDefault_eq_dec: forall {T: Set}, EqDecision T -> EqDecision (OrDefault T).
Proof. solve_decision. Defined.

#[global] Instance OrDefault_is_dependent {T : Set} `{!names.IsDependent T} :
    IsDependent (OrDefault T) :=
  fun x => if x is UserDefined t then is_dependent t else false.
