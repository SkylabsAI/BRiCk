(*
 * Copyright (c) 2020-21 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.prelude Require Import bytestring telescopes.
From bedrock.lang.cpp.semantics Require Import values.
From bedrock.lang.cpp.logic Require Import spec pred.
(* XXX only needed for examples. *)
Require bedrock.lang.cpp.heap_notations.
From bedrock.lang.cpp.logic Require heap_pred.

Set Universe Polymorphism.

Declare Scope fspec_scope.
Delimit Scope fspec_scope with fspec.
Bind Scope fspec_scope with WithPrePost.

Module V1.
  Parameter PROP : bi.

  Definition WPP := (list val -> Prop) -> (val -> PROP) -> PROP.

  Definition add_arg (s : names.ident) (v : val) (wpp : WPP) : WPP :=
    fun argsP post => wpp (fun args => argsP (v :: args)) post.
  Definition add_pre (P : PROP) (wpp : WPP) : WPP :=
    fun argsP post => wpp argsP post ** P.
  Definition add_post (P : PROP) (wpp : WPP) : WPP :=
    fun argsP post => wpp argsP (fun result => P -* post result).
  Definition add_with {T : Type} (wpp : T -> WPP) : WPP :=
    fun argsP post => Exists (x : T), wpp x argsP post.
  Definition post_ret (v : val) (Q : PROP) : WPP :=
    fun argP post => [| argP nil |] ** (Q -* post v).
  Definition finish (wpp : WPP) : list val -> (val -> PROP) -> PROP :=
    fun vs post => wpp (eq vs) post.

  Parameters PRE POST RET : PROP.
  Eval cbv beta iota zeta delta -[bi_wand bi_sep bi_emp] in
      add_with (fun x : ptr => add_arg "x" (Vptr x) (add_pre PRE (add_post POST (post_ret (Vint 0) RET)))).
End V1.

Module V2.
  Parameter PROP : bi.

  Definition WPP := (list val -> ((val -> PROP) -> PROP) -> PROP) -> PROP.

  Definition add_arg (s : names.ident) (v : val) (wpp : WPP) : WPP :=
    fun Q => wpp $ fun args post => Q (v :: args) post.
  Definition add_pre (P : PROP) (wpp : WPP) : WPP :=
    fun Q => wpp $ fun args post => P -* Q args post.
  Definition add_post (P : PROP) (wpp : WPP) : WPP :=
    fun Q => wpp $ fun args post => Q args (fun result => P -* post result).
  Definition add_with {T : Type} (wpp : T -> WPP) : WPP :=
    fun Q => Forall x : T, wpp x Q.
  Definition post_ret {t : tele} (v : t -t> val) (P : t -t> PROP) : WPP :=
    fun Q => Q nil (fun XX => telescopes.bi_tforall (fun x : t => tele_app P x -* XX (tele_app v x))).
  Definition finish (RET : ((val -> PROP) -> PROP) -> PROP) (wpp : WPP) : list val -> (val -> PROP) -> PROP.
    refine (fun vs post => wpp (fun vs' post' => [| vs = vs' |] ** RET (fun retP => post' (fun v => retP v -* post v)))).
  Defined.

  Parameters PRE POST RET : PROP.
  Eval cbv beta iota zeta delta -[bi_wand bi_sep bi_emp] in
      fun RETURN => finish RETURN $ add_with (fun x : ptr => add_arg "x" (Vptr x) (add_pre PRE (add_post POST (post_ret (t:=TeleS (fun _ : Z => TeleO)) (fun z => Vint z) (fun z => RET))))).

End V2.


Section with_Σ.
  Context `{PROP : bi}.

  Local Notation WithPrePost := (WithPrePost PROP) (only parsing).

  Definition add_pre (P : PROP) (wpp : WithPrePost) : WithPrePost :=
    fun args Q => P ** wpp args Q.

  Definition add_args (ls : list val) (wpp : WithPrePost) : WithPrePost :=
    fun args Q => Exists args', [| args = ls ++ args' |] ** wpp args' Q.

  Definition add_arg (s : names.ident) (v : val) (wpp : WithPrePost) : WithPrePost :=
    fun args Q => Exists args', [| args = v :: args' |] ** wpp args' Q.

  Definition add_post (P : PROP) (wpp : WithPrePost) : WithPrePost :=
    fun args Q => wpp args (fun res => P ** Q res).

  Definition add_require (P : Prop) (wpp : WithPrePost) : WithPrePost :=
    fun args Q => [| P |] ** wpp args Q.

  Definition add_persist (P : PROP) (wpp : WithPrePost) : WithPrePost :=
    fun args Q => □ P ** wpp args Q.

  Definition add_prepost (P : PROP) (wpp : WithPrePost) : WithPrePost :=
    add_pre P (add_post P wpp).

  Definition post_void (t : tele) (Q : t -t> PROP) : WithPrePost :=
    fun args Q' => [| args = nil |] ** (telescopes.bi_tforall (fun args => tele_app Q args -* Q' Vvoid))%I.

  Definition post_ret (t : tele) (Q : t -t> val * PROP) : WithPrePost :=
    fun args Q' => [| args = nil |] ** (telescopes.bi_tforall (fun exs => let '(v,P) := tele_app Q exs in P -* Q' v))%I.

  Definition add_with {t : tele} (wpp : t -t> WithPrePost) : WithPrePost :=
    fun args Q => telescopes.bi_texist (fun exs => tele_app wpp exs args Q).

  Definition with_tele (t : telescopes.tele) (f : telescopes.tele_arg t -> WithPrePost)
  : WithPrePost :=
    @add_with (telescopes.TeleS (fun x : telescopes.tele_arg t => telescopes.TeleO)) f.

  (* Markers to help notation printing. *)
  Definition let_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_arg_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_pre_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_prepost_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_require_fspec (X : WithPrePost) : WithPrePost := X.

  Definition with_persist_fspec (X : WithPrePost) : WithPrePost := X.

  Definition exactWpp (wpp : WithPrePost) : WithPrePost := wpp.

End with_Σ.

Arguments with_tele _ _ _ : clear implicits.

Strategy expand
   [ add_pre add_args add_require add_arg add_post add_prepost with_tele ].
(** Make sure to list all identity functions above. And in the same order, for clarity. *)
Strategy expand
   [ let_fspec with_arg_fspec with_pre_fspec with_prepost_fspec with_require_fspec with_persist_fspec exactWpp ].

Notation "'\with' x .. y X" :=
  (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
            (fun x => .. (fun y => X%fspec) ..))
  (at level 10, x closed binder, y closed binder, X at level 200, right associativity,
   format "'[v' '\with'     '[hv' x  ..  y ']'  '//' X ']'").

Notation "'\withT' ts <- t X" := (@with_tele _ t (fun ts => X))
  (at level 200, ts name, X at level 200, right associativity,
   format "'[v' '\withT'     ts <- t  '//' X ']'").

Notation "'\prepost' pp X" :=
  (@add_prepost _ pp%I X%fspec)
  (at level 10, pp at level 100, X at level 200, right associativity,
   format "'[v' '[hv  ' '\prepost'  '/' pp ']' '//' X ']'").

Notation "'\prepost{' x .. y '}' pp X" :=
  (with_prepost_fspec ((@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => @add_prepost _ pp%I X%fspec) .. ))))
  (at level 10, x binder, y binder, pp at level 100, X at level 200, right associativity,
   format "'[v' '[hv  ' '\prepost{' x  ..  y '}'  '/' pp ']' '//' X ']'").

Notation "'\let' x ':=' e X" :=
  (let_fspec (let x := e in X%fspec))
  (at level 10, x pattern, e at level 150, X at level 200, right associativity,
   format "'[v' '[hv  ' '\let'      x  ':='  '/' e ']' '//' X ']'").

Notation "'\args' ls X" :=
  (@add_args _ ls%list X%fspec)
  (at level 10, X at level 200, right associativity,
   format "'[v' '[hv  ' '\args'     '/' ls  ']' '//' X ']'").

Notation "'\args{' x .. y '}' ls X" :=
  (@with_arg_fspec _ (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => (@add_args _ ls%list X%fspec)) .. )))
  (at level 10, x binder, y binder, X at level 200, right associativity,
   format "'[v' '[hv  ' '\args{' x  ..  y '}'  '/' ls  ']' '//' X ']'").

Notation "'\arg' nm v X" :=
  (@add_arg _ nm%bs v X%fspec)
  (at level 10, nm at level 0, X at level 200, right associativity,
   format "'[v' '\arg'  nm  v  '//' X ']'").

Notation "'\arg{' x .. y } nm v X" :=
  (@with_arg_fspec _ (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
                                (fun x => .. (fun y => (@add_arg _ nm%bs v X%fspec)) .. )))
  (at level 10, nm at level 0, x binder, y binder, X at level 200, right associativity,
   format "'[v' '\arg{' x  ..  y '}'  nm  v  '//' X ']'").

Notation "'\require' pre X" :=
  (@add_require _ pre X%fspec)
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '[' '\require'  pre ']' '//' X ']'").

Notation "'\require{' x .. y } pre X" :=
  (@with_require_fspec _ (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
                                (fun x => .. (fun y => (@add_require _ pre X%fspec)) .. )))
  (at level 10, pre at level 200, x binder, y binder, X at level 200, left associativity,
   format "'[v' '\require{' x  ..  y '}'  pre  '//' X ']'").

Notation "'\persist' pre X" :=
  (@add_persist _ pre%I X%fspec)
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '[' '\persist'  pre ']' '//' X ']'").

Notation "'\persist{' x .. y } pre X" :=
  (@with_persist_fspec _ (@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
                                (fun x => .. (fun y => (@add_persist _ pre%I X%fspec)) .. )))
  (at level 10, pre at level 200, x binder, y binder, X at level 200, left associativity,
   format "'[v' '\persist{' x  ..  y '}'  pre  '//' X ']'").

Notation "'\pre' pre X" :=
  (@add_pre _ pre%I X%fspec)
  (at level 10, pre at level 200, X at level 200, left associativity,
   format "'[v' '[  ' '\pre'  '/' pre  ']' '//' X ']'").

Notation "'\pre{' x .. y '}' pp X" :=
  (with_pre_fspec ((@add_with _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) .. ))
                                (fun x => .. (fun y => @add_pre _ pp%I X%fspec) .. ))))
  (at level 10, x binder, y binder, pp at level 100, X at level 200, right associativity,
   format "'[v' '[hv  ' '\pre{' x  ..  y '}'  '/' pp ']' '//' X ']'").

Notation "'\post' { x .. y } [ r ] post" :=
  (@post_ret _ (TeleS (fun x => .. (TeleS (fun y => TeleO)) ..))
             (fun x => .. (fun y => (r, post%I)) ..))
  (at level 10, r at level 200, no associativity, x binder, y binder,
   post at level 200,
   format "'[v' '\post' { x  ..  y } [ r ]  '//'          '[hv ' post ']' ']'").

Notation "'\post' { } [ r ] post" :=
  (@post_ret _ TeleO (r, post%I))
  (at level 10, r at level 200, no associativity,
   post at level 200, only parsing).

Notation "'\post' [ r ] post" :=
  (@post_ret _ TeleO (r, post%I))
  (at level 10, r at level 200, no associativity,
   post at level 200,
   format "'[v' '\post' [ r ]  '//'          '[hv ' post ']' ']'").

Notation "'\post' post" :=
  (@post_void _ TeleO post%I)
  (at level 10, no associativity,
   post at level 200,
   format "'[v' '\post'     '[hv ' post ']' ']'").

Notation "'\exact' wpp" := (exactWpp wpp)
  (at level 10, wpp at level 200).

Section with_Σ.
  Context `{Σ : cpp_logic ti}.

  Import heap_notations heap_pred.

  Declare Reduction red_spec :=
    cbv beta iota zeta delta [ add_pre post_void telescopes.bi_tforall tele_fold tele_bind tele_app ].

  Example _1 : WithPrePost mpredI :=
    \pre emp
    \post  emp.
  Eval cbv beta iota zeta delta [ _1 add_pre post_void telescopes.bi_tforall tele_fold tele_bind tele_app ] in _1.

  Example _2 : WithPrePost mpredI :=
   \with (I J : mpred) (p : ptr) (R : Qp -> Qp -> nat -> Rep)
   \prepost emp
   \require True
   \require{x} x = 1
   \arg{n (nn: nat)} "foo" (Vint n)
   \args{a} [Vint (Z.of_nat a)]
   \with (z : nat)
   \prepost emp
   \prepost{q1 q2} p |-> R q1 q2 0
   \pre{q3 q4} p |-> R q3 q4 0
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post {x} [ Vint x ] emp.

  Eval cbv beta iota zeta delta [ _2 add_pre post_void telescopes.bi_tforall tele_fold tele_bind tele_app add_prepost add_persist add_require add_with telescopes.bi_texist add_post with_require_fspec with_arg_fspec add_arg add_args with_prepost_fspec with_pre_fspec post_ret
                                ] in _2.

  Example _3 : WithPrePost mpredI :=
    \with (I J : mpred)
    \with  (a : nat)
    \prepost emp
    \with (z : nat)
    \prepost emp
    \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
    \post{r}[ r ] emp.

  Example _4 : WithPrePost mpredI :=
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
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post emp.

  Example _5 : WithPrePost mpredI :=
    \pre emp ** Exists y : nat, [| y = 3 |]
    \post{}[Vptr nullptr] emp.

  Example _6 : WithPrePost mpredI :=
    \pre |==> True ** |={∅,⊤}=> False
    \post{}[Vptr nullptr] emp.

End with_Σ.
