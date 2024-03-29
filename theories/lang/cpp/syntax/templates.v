Require Import bedrock.prelude.base.
Require Import bedrock.lang.cpp.syntax.core.

(** ** Template pre-instances *)
(**
A template file maps the symbol or type name of a template
instantiation (bound in a translation unit) to a _template
pre-instance_ comprising the instance's template name (bound in a
template file) and arguments.
*)
Definition temp_name : Set := name' lang.temp.

Section tpreinst.
  Context {lang : lang.t}.

  (* TODO: this type probably does not need to be parametric in [lang.t]
     The only meaningful instantation is [lang.cpp]
   *)
  Record tpreinst' : Set := TPreInst {
    tpreinst_name : temp_name;
    tpreinst_args : list (temp_arg' lang);
  }.

  #[global] Instance tpreinst'_inhabited : Inhabited tpreinst'.
  Proof. solve_inhabited. Qed.

  #[global] Instance tpreinst'_eq_dec : EqDecision tpreinst'.
  Proof. solve_decision. Defined.
End tpreinst.
Add Printing Constructor tpreinst'.
#[global] Arguments tpreinst' : clear implicits.
#[global] Arguments TPreInst {_} _ & _ : assert.

(** ** Template instances *)
Section tinst.
  #[local] Set Universe Polymorphism.
  #[local] Set Polymorphic Inductive Cumulativity.
  #[local] Unset Auto Template Polymorphism.
  Universe uV.
  Context {lang : lang.t} {V : Type@{uV}}.

  Record tinst' : Type@{uV} := TInst {
    tinst_params : list (temp_param' lang.temp);
    tinst_args : list (temp_arg' lang);
    tinst_value : V;
  }.

  #[global] Instance tinst'_inhabited `{!Inhabited V} : Inhabited tinst'.
  Proof. solve_inhabited. Qed.

  #[global] Instance tinst'_eq_dec
      `{!EqDecision V} :
    EqDecision tinst'.
  Proof. solve_decision. Defined.
End tinst.
Add Printing Constructor tinst'.
#[global] Arguments tinst' : clear implicits.
#[global] Arguments TInst {_ _} _ _ & _ : assert.

Notation temp_param := (temp_param' lang.cpp).
Notation temp_arg := (temp_arg' lang.cpp).
