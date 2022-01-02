(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.prelude Require Import bytestring telescopes.
From bedrock.lang.cpp.semantics Require Import values.
From bedrock.lang.cpp.logic Require Import pred.
Require Import bedrock.lang.cpp.specs.with_pre_post.
From bedrock.lang.cpp.specs Require Import spec_notations.

#[local] Set Universe Polymorphism.
Set Printing Universes.

(** Pre-specifications are "old-style" specifications that are based on passing
    (and returning) [val].

    These are elaborated into specifications that take pointers.
 *)
Declare Scope pre_spec_scope.
Delimit Scope pre_spec_scope with pre_spec.
Bind Scope pre_spec_scope with WithPrePost.
Bind Scope pre_spec_scope with WithPrePostG.

Section pre_specs.
  Context `{PROP : bi}.

  Polymorphic Universes X Z Y.

  Set Printing Universes.
  Definition add_arg@{} (s : names.ident) (v : val) (wpp : WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val :=
    {| wpp_with := wpp.(wpp_with)
     ; wpp_pre  := tele_map (fun '(args,X) => (v :: args, X)) wpp.(wpp_pre)
     ; wpp_post := wpp.(wpp_post)
    |}.

  Definition post_void@{u} {t : tele} (Q : tele_fun@{X u u} t PROP) : WithPrePostG@{X Z Y Set Set} PROP (list val) val :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp)%I
     ; wpp_post := {| we_ex := t
                    ; we_post := tele_map (fun Q => (Vvoid, Q)) Q |} |}.

  Definition post_ret {t : tele} (Q : t -t> val * PROP) : WithPrePostG@{X Z Y Set Set} PROP (list val) val  :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp)%I
     ; wpp_post := {| we_ex := t
                    ; we_post := Q |} |}.

  (*
  Definition with_tele (t : telescopes.tele) (f : telescopes.tele_arg t -> WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val :=
    add_with@{X Z Y Set Set} (t:=telescopes.TeleS (fun x : telescopes.tele_arg t => telescopes.TeleO)) f.
   *)

  (* Markers to help notation printing. *)
  Definition let_pre_spec@{} (X : WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val := X.

  Definition with_arg_pre_spec@{} (X : WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val := X.

  Definition with_pre_pre_spec (X : WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val := X.

  Definition with_prepost_pre_spec (X : WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val := X.

  Definition with_require_pre_spec (X : WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val := X.

  Definition with_persist_pre_spec (X : WithPrePostG@{X Z Y Set Set} PROP (list val) val)
    : WithPrePostG@{X Z Y Set Set} PROP (list val) val := X.

  Definition exactWpp@{A R} {A R} (wpp : WithPrePostG@{X Z Y A R} PROP A R)
    : WithPrePostG@{X Z Y A R} PROP A R := wpp.

End pre_specs.

(* Arguments with_tele _ _ _ : clear implicits. *)

Strategy expand
   [ add_pre add_require add_arg add_post add_prepost (* with_tele *) ].
(** Make sure to list all identity functions above. And in the same order, for clarity. *)
Strategy expand
   [ let_pre_spec with_arg_pre_spec with_pre_pre_spec with_prepost_pre_spec with_require_pre_spec with_persist_pre_spec exactWpp ].

Notation "'\with' x .. y X" :=
  (add_with (t:=TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
            (fun x => .. (fun y => X%pre_spec) ..)).

(* Notation "'\withT' ts <- t X" := (@with_tele _ t (fun ts => X)). *)

Notation "'\prepost' pp X" := (add_prepost pp%I X%pre_spec).

Notation "'\prepost{' x .. y '}' pp X" :=
  (with_prepost_pre_spec ((add_with (t:=TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => add_prepost pp%I X%pre_spec) .. )))).

Notation "'\let' x ':=' e X" := (let_pre_spec (let x := e in X%pre_spec)).

Notation "'\arg' nm v X" := (add_arg nm%bs v X%pre_spec).

Notation "'\arg{' x .. y } nm v X" :=
  (with_arg_pre_spec (add_with (t:=TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
                                (fun x => .. (fun y => (add_arg nm%bs v X%pre_spec)) .. ))).

Notation "'\require' pre X" := (add_require pre X%pre_spec).

Notation "'\require{' x .. y } pre X" :=
  (with_require_pre_spec (add_with (t:=TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
                                (fun x => .. (fun y => (add_require pre X%pre_spec)) .. ))).

Notation "'\persist' pre X" := (add_persist pre%I X%pre_spec).

Notation "'\persist{' x .. y } pre X" :=
  (with_persist_pre_spec (add_with (t:=TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
                                (fun x => .. (fun y => (add_persist pre%I X%pre_spec)) .. ))).

Notation "'\pre' pre X" := (add_pre pre%I X%pre_spec).

Notation "'\pre{' x .. y '}' pp X" :=
  (with_pre_pre_spec ((add_with (t:=TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => add_pre pp%I X%pre_spec) .. )))).

Notation "'\post' { x .. y } [ r ] post" :=
  (post_ret (t:=TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
             (fun x => .. (fun y => (r, post%I)) ..)).

Notation "'\post' { } [ r ] post" :=
  (post_ret (t:=TeleO) (r, post%I)).

Notation "'\post' [ r ] post" :=
  (@post_ret _ TeleO (r, post%I)).

Notation "'\post' post" :=
  (@post_void _ TeleO post%I).

Notation "'\exact' wpp" := (exactWpp wpp).

Section with_Σ.
  Context `{Σ : cpp_logic ti}.

  Import heap_notations heap_pred.
  #[local] Notation WPP := (WithPrePostG mpredI (list val) val).

  Fail Fail Definition _1 : WPP :=
    \pre emp
    \post  emp.

  Fail Fail Definition _2 : WPP :=
    \with (I J : mpred) (p : ptr) (R : Qp -> Qp -> nat -> Rep)
    \prepost emp
    \require True
    \require{x} x = 1
    \arg{n (nn: nat)} "foo" (Vint n)
    \with (z : nat) (a : nat)
    \prepost emp
    \prepost{q1 q2} p |-> R q1 q2 0
    \pre{q3 q4} p |-> R q3 q4 0
    \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
    \post {x} [ Vint x ] emp.

  Fail Fail Definition _3 : WPP :=
   \with (I J : mpred)
   \with  (a : nat)
   \prepost emp
   \with (z : nat)
   \prepost emp
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post{r}[ r ] emp.

  Fail Fail Definition _4 : WPP :=
   \with (I J : mpred) (n : nat)
   \with  (a : nat)
   \let x := 3%nat
   \with (lm : nat * nat)
   \let (l,m) := lm
   \require l+m = 3
   \prepost emp
   \persist emp
   \persist{n1} [| n1 = 1 |]
   \persist{n2} [| n2 = 1 |]%N
   \persist{z} [| z = 1 |]%Z
   \with (z : nat)
   \arg{(zz : Z)} "foo" (Vint zz)
   \prepost emp
   \with (zzz : Type)
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post emp.

  Fail Fail Definition _5 : WPP :=
    \pre emp ** Exists y : nat, [| y = 3 |]
    \post{}[Vptr nullptr] emp.

  Fail Fail Definition _6 : WPP :=
    \pre |==> True ** |={∅,⊤}=> False
    \post{}[Vptr nullptr] emp.

End with_Σ.
