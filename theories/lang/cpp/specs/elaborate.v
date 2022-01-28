(*
 * Copyright (c) 2021 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Functionality to elaborate specifications that are written to take
    operands (i.e. [val]) and convert them to take materialized values.

    We implement this using ad-hoc polymorphism (i.e. type classes) because:
    1. the implementation requires matching under lambdas.
    2. the implementation is complex due to the telescopes.
 *)

Require Import bedrock.prelude.telescopes.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.
Require Import bedrock.lang.cpp.specs.with_pre_post.
Require Import bedrock.lang.cpp.specs.cpp_specs.

Section with_cpp.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  #[local] Set Universe Polymorphism.
  #[local] Unset Universe Minimization ToSet.
  Set Printing Universes.
  (* )Unset Printing Notations. (* useful if you need to look at universe annotations *) *)

  Polymorphic Universes X Z Y.
  (* Universe in notations are refreshed, so this does not work *)
  (* #[local] Notation WPP := (WithPrePostG@{X Z Y Set Set} mpredI). *)

  Definition add_prim_arg@{R u} {R : Type@{R}} (t : type) (s : names.ident) (v : val)
             (wpp : WithPrePostG@{X Z Y Set R} mpredI (list ptr) R)
  : WithPrePostG@{X Z Y Set R}  mpredI (list ptr) R :=
    add_with@{X Z Y Set R u} (t:=TeleS (fun _ : ptr => TeleO))
             (fun p : ptr => with_pre_post.add_arg (A:=ptr) s p (add_pre (_at p (primR t 1 v))
                                                                      (with_pre_post.add_post (_at p (anyR t 1)) wpp))).


  Definition post_prim_ret@{A} {A : Type@{A}} (ty : type) (t : tele@{X}) (Q : tele_fun@{X Z Z} t (val * mpredI))
  : WithPrePostG@{X Z Y A Set} mpredI (list A) ptr :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp)%I
     ; wpp_post := {| we_ex := TeleS (fun _ : ptr => t)
                    ; we_post := fun p => tele_map@{_ _ _ _ X} (fun '(v,Q) => (p, _at p (primR ty 1 v) ** Q)) Q |} |}.

  Definition post_prim_void@{A} {A : Type@{A}} (ty : type) (t : tele@{X}) (Q : tele_fun@{X Z Z} t mpredI)
  : WithPrePostG@{X Z Y A Set} mpredI (list A) ptr :=
    {| wpp_with := TeleO
     ; wpp_pre := (nil, emp)%I
     ; wpp_post := {| we_ex := TeleS (fun _ : ptr => t)
                    ; we_post := fun p => tele_map@{_ _ _ _ X} (fun Q => (p, _at p (primR Tvoid 1 Vvoid) ** Q)) Q |} |}.

  Class Elaborate (ts : list type) (rt : type) (wpp : WithPrePostG@{X Z Y Set Set} mpredI (list val) val) :=
    cpp_spec : WithPrePostG@{X Z Y Set Set} mpredI (list ptr) ptr.

  Section parametric.
    Variables (ts : list type) (rt : type).
    #[local] Notation Elaborate := (Elaborate ts rt).

    #[global] Instance add_with_Elaborate {t} `{X : tforallT (fun args => Elaborate (tele_app wpp args))}
      : Elaborate (add_with (t:=t) wpp) :=
      add_with (t:=t) (tele_bind (fun args => @cpp_spec _ _ _ (tapplyT _ X args))).

    #[global] Instance add_require_Elaborate {P} `{Elaborate wpp} : Elaborate (add_require P wpp) :=
      add_require P cpp_spec.

    #[global] Instance add_persist_Elaborate {P} `{Elaborate wpp} : Elaborate (add_persist P wpp) :=
      add_persist P cpp_spec.

    #[global] Instance add_pre_Elaborate {P} `{Elaborate wpp} : Elaborate (add_pre P wpp) :=
      add_pre P cpp_spec.

    #[global] Instance add_post_Elaborate {P} `{Elaborate wpp} : Elaborate (add_post P wpp) :=
      add_post P cpp_spec.

    #[global] Instance add_prepost_Elaborate {P} `{Elaborate wpp} : Elaborate (add_prepost P wpp) :=
      add_prepost P cpp_spec.

    #[global] Instance let_pre_spec_Elaborate {wpp} {X : Elaborate wpp} : Elaborate (let_pre_spec wpp) :=
      X.

  End parametric.

  Section with_R.
    Polymorphic Universe R.
    Variable R : Type@{R}.

    (** This class provides a mechanism to elaborate an argument *)
    Class ElaborateArg@{X Z Y} (ty : type) (x : names.ident) (v : val) : Type :=
      elaborated_arg : WithPrePostG@{X Z Y Set R} mpredI (list ptr) R -> WithPrePostG@{X Z Y Set R} mpredI (list ptr) R.

    #[global] Instance Tint_ElaborateArg  {sz sgn x v} : ElaborateArg (Tint sz sgn) x v :=
      add_prim_arg (Tint sz sgn) x v.
    #[global] Instance Tptr_ElaborateArg {ty x v} : ElaborateArg (Tptr ty) x v :=
      add_prim_arg (Tptr $ erase_qualifiers ty) x v.
    #[global] Instance Tbool_ElaborateArg {x v} : ElaborateArg Tbool x v :=
      add_prim_arg Tbool x v.
    #[global] Instance Tnamed_ElaborateArg {cls x p} : ElaborateArg (Tnamed cls) x (Vptr p) :=
      with_pre_post.add_arg x p.

    #[global] Instance Tref_ElaborateArg {ty x p} : ElaborateArg (Tref ty) x (Vref p) :=
      add_prim_arg (Tref $ erase_qualifiers ty) x (Vref p).
    #[global] Instance Trv_ref_ElaborateArg {ty x p} : ElaborateArg (Trv_ref ty) x (Vref p) :=
      add_prim_arg (Tref $ erase_qualifiers ty) x (Vref p).

    #[global] Instance Qmut_ElaborateArg {ty x v} (E : ElaborateArg ty x v) : ElaborateArg (Qmut ty) x v :=
      elaborated_arg.
    #[global] Instance Qconst_ElaborateArg {ty x v} (E : ElaborateArg ty x v) : ElaborateArg (Qconst ty) x v :=
      elaborated_arg.
    #[global] Instance Qconst_volatile_ElaborateArg {ty x v} (E : ElaborateArg ty x v) : ElaborateArg (Qconst_volatile ty) x v :=
      elaborated_arg.
    #[global] Instance Qmut_volatile_ElaborateArg {ty x v} (E : ElaborateArg ty x v) : ElaborateArg (Qmut_volatile ty) x v :=
      elaborated_arg.

  End with_R.
  Arguments elaborated_arg {_ _ _ _ _} _.

  #[global] Instance add_arg_Elaborate {ty ts rt} {x} {v : val} `{ElaborateArg _ ty x v} `{Elaborate ts rt wpp}
    : Elaborate (ty :: ts) rt (add_arg x v wpp) :=
    elaborated_arg cpp_spec.

  #[global] Instance post_ret_int_Elaborate {sz sgn} t Q
    : Elaborate nil (Tint sz sgn) (post_ret (t:=t) Q) :=
    @post_prim_ret _ (Tint sz sgn) t Q.

  #[global] Instance post_ret_bool_Elaborate t Q
    : Elaborate nil Tbool (post_ret (t:=t) Q) :=
    @post_prim_ret _ Tbool t Q.

  #[global] Instance post_ret_ptr_Elaborate ty t Q
    : Elaborate nil (Tptr ty) (post_ret (t:=t) Q) :=
    @post_prim_ret _ (Tptr ty) t Q.

  #[global] Instance post_ret_ref_Elaborate ty t Q
    : Elaborate nil (Tref ty) (post_ret (t:=t) Q) :=
    @post_prim_ret _ (Tref ty) t Q.

  #[global] Instance post_ret_rv_ref_Elaborate ty t Q
    : Elaborate nil (Trv_ref ty) (post_ret (t:=t) Q) :=
    @post_prim_ret _ (Trv_ref ty) t Q.

  #[global] Instance post_void_Elaborate t (Q : tele_fun@{X Z Z} _ _)
    : Elaborate nil Tvoid (post_void (t:=t) Q) :=
    @post_prim_void _ Tvoid t Q.

  #[global] Instance post_void_qual_Elaborate ty tq t (Q : tele_fun@{X Z Z} _ _) (X : Elaborate nil ty (post_void (t:=t) Q))
    : Elaborate nil (Tqualified tq ty) (post_void (t:=t) Q) :=
    X.

  #[global] Instance post_ret_qual_Elaborate ty tq t (Q : tele_fun@{X Z Z} _ _) (X : Elaborate nil ty (post_ret (t:=t) Q))
    : Elaborate nil (Tqualified tq ty) (post_ret (t:=t) Q) :=
    X.

End with_cpp.

#[global] Hint Mode Elaborate - - + + ! : typeclass_instances.

Arguments cpp_spec {_ Σ} ts%list_scope rt wpp%pre_spec {_}.

#[global] Hint Extern 0 (tforallT ?X) => cbn [ tforallT tele_app ] ; intros : typeclass_instances.

#[global] Hint Opaque add_arg post_ret post_void add_pre add_post add_prepost add_require add_with let_pre_spec : typeclass_instances.

Section tests.
  Context `{Σ : cpp_logic}.
  Context {σ : genv}.

  Goal forall p q OPAQUE,
      OPAQUE (cpp_spec (Tint W64 Signed :: Tptr (Tnamed "X") :: nil) (Tint W64 Signed)
                         (add_arg "x" (Vint 0) (add_arg "y" (Vptr p) (post_ret (t:=TeleO) (Vint q, emp%I))))).
  Proof.
    rewrite /add_arg_Elaborate/post_ret_int_Elaborate/cpp_spec/elaborated_arg/Tint_ElaborateArg/Tptr_ElaborateArg/=.
  Abort.

  Goal forall p OPAQUE,
      OPAQUE (cpp_spec (Σ:=Σ) (Tint W64 Signed :: Tptr (Tnamed "X") :: nil) Tvoid
                         (add_with (t:=TeleS (fun _ => TeleO))
                                   (fun z => add_arg "x" (Vint z)
                                                  (add_arg "y" (Vptr p) (post_void (t:=TeleO) (emp%I)))))).
  Proof.
    rewrite /add_with_Elaborate/add_arg_Elaborate/post_void_Elaborate/cpp_spec/elaborated_arg/Tint_ElaborateArg/Tptr_ElaborateArg/=.
  Abort.

End tests.
