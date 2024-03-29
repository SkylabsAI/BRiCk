(*
 * Copyright (c) 2020-2024 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.syntax.core.
Require Import bedrock.prelude.bytestring.

Set Primitive Projections.

Variant SwitchBranch : Set :=
| Exact (_ : Z)
| Range (_ _ : Z).
#[global] Instance: EqDecision SwitchBranch.
Proof. solve_decision. Defined.

Inductive VarDecl' {lang} : Set :=
| Dvar (name : localname) (_ : type' lang) (init : option (Expr' lang))
| Ddecompose (_ : Expr' lang) (anon_var : ident) (_ : list VarDecl')
  (* initialization of a function-local [static]. See https://eel.is/c++draft/stmt.dcl#3 *)
| Dinit (thread_safe : bool) (name : name' lang) (_ : type' lang) (init : option (Expr' lang)).
#[global] Arguments VarDecl' _ : clear implicits, assert.
#[global] Instance VarDecl_eq_dec {lang} : EqDecision (VarDecl' lang).
Proof.
  refine (fix dec (x y : VarDecl' lang) : {x = y} + {x <> y} :=
            let _ : EqDecision _ := dec in
            match x as x , y as y return {x = y} + {x <> y} with
            | Ddecompose xi xx xs , Ddecompose yi yx ys =>
              match decide (xs = ys) with
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
Notation VarDecl := (VarDecl' lang.cpp).

Inductive Stmt' {lang} : Set :=
| Sseq    (_ : list Stmt')
| Sdecl   (_ : list (VarDecl' lang))

| Sif     (_ : option (VarDecl' lang)) (_ : Expr' lang) (_ _ : Stmt')
| Swhile  (_ : option (VarDecl' lang)) (_ : Expr' lang) (_ : Stmt')
| Sfor    (_ : option Stmt') (_ : option (Expr' lang)) (_ : option (Expr' lang)) (_ : Stmt')
| Sdo     (_ : Stmt') (_ : Expr' lang)

| Sswitch (_ : option (VarDecl' lang)) (_ : Expr' lang) (_ : Stmt')
| Scase   (_ : SwitchBranch)
| Sdefault

| Sbreak
| Scontinue

| Sreturn (_ : option (Expr' lang))

| Sexpr   (_ : Expr' lang)

| Sattr (_ : list ident) (_ : Stmt')

| Sasm (_ : bs) (volatile : bool)
       (inputs : list (ident * (Expr' lang)))
       (outputs : list (ident * (Expr' lang)))
       (clobbers : list ident)

| Slabeled (_ : ident) (_ : Stmt')
| Sgoto (_ : ident)
| Sunsupported (_ : bs).
#[global] Arguments Stmt' _ : clear implicits, assert.
#[global] Instance Stmt_eq_dec {lang} : EqDecision (Stmt' lang).
Proof.
  rewrite /RelDecision /Decision.
  fix IHs 1.
  rewrite -{1}/(EqDecision _) in IHs.
  decide equality; try solve_trivial_decision.
Defined.
Notation Stmt := (Stmt' lang.cpp).
Notation MStmt := (Stmt' lang.temp).

Definition Sskip {lang} : Stmt' lang := Sseq nil.

