(*
 * Copyright (c) 2022 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** Functionality to elaborate specifications that are written to take
    operands (i.e. [val]) and convert them to take materialized values.
 *)
From bedrock.lang.cpp Require Import ast logic semantics.
From bedrock.lang.cpp.specs Require Import cpp_specs wp_spec_compat.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** determine if an argument is already materialized in the operand style.

      NOTE arrays are treated as primitives because they are passed as pointers
   *)
  Definition mtype (t : type) : globname + type :=
    match erase_qualifiers t with
    | Tnamed cls => inl cls
    | Trv_ref ty => inr (Tref ty)
    | ty => inr ty
    end.

  (** [elaborate ret ts wpp args] builds a function specification around [wpp]
      assuming that [wpp] takes the arguments in [args] (in reverse order) and the
      remaining arguments in [ts].
   *)
  Fixpoint elaborate (ret : type) (ts : list type) (args : list val) (wpp : WpSpec_cpp_val) : WpSpec mpredI ptr ptr :=
    match ts with
    | nil =>
        match mtype ret with
        | inl cls =>
            wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr => DONE pr [| Vptr pr = rv |]))
        | inr t =>
            wp_spec_bind wpp args (fun rv => WITH (fun pr : ptr => DONE pr (_at pr (primR t 1 rv))))
        end
    | t :: ts =>
        match mtype t with
        | inl cls =>
            add_with (fun pv : ptr => add_arg pv (elaborate ret ts (args ++ [Vptr pv]) wpp))
        | inr t =>
            add_with (fun pv : ptr => add_with (fun v : val => add_arg pv (
                                           add_pre (_at pv (primR t 1 v)) (add_post (Exists v, _at pv (primR t 1 v))
                                                                                    (elaborate ret ts (args ++ [v]) wpp)))))
        end
    end.

  (** [cpp_spec ret ts spec] is the elaborated version of the [spec]
      (operand-based) spec that is based on materialized values.
   *)
  Definition cpp_spec (ret : type) (ts : list type) : WpSpec_cpp_val -> WpSpec_cpp_ptr :=
    elaborate ret ts nil.

  (** * Theory *)


  #[global] Instance elaborate_ne n ret ts : forall vs,
    Proper (dist n ==> dist n) (elaborate ret ts vs).
  Proof.
    induction ts; simpl; intros.
    { case_match;  do 3 red; intros; apply wp_spec_bind_ne; eauto.
      do 5 red. simpl; intros; subst.
      f_equiv. f_equiv.
      f_equiv. apply H1.
      do 5 red; intros; subst. simpl. f_equiv.
      red; intros. f_equiv. apply H1. }
    { red. red.
      case_match; intros; f_equiv.
      { red. intros; f_equiv. apply IHts. auto. }
      { red; intros; f_equiv. red. intros.
        f_equiv. f_equiv. f_equiv. apply IHts. auto. } }
  Qed.

End with_cpp.
