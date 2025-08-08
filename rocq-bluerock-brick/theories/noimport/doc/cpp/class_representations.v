(*
 * Copyright (c) 2020-2024 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import bluerock.iris.extra.bi.prelude.
Require Import bluerock.iris.extra.proofmode.proofmode.
Require Import bluerock.lang.cpp.cpp.
Require Import bluerock.lang.cpp.parser.plugin.cpp2v.

Section with_Σ.
  Context `{Σ : cpp_logic} {σ : genv}.

  (** * Struct & Class

      consider the following C++ class.
 *)
  cpp.prog source prog cpp:{{
        class Point {
          int x;
          int y;
        };
  }}.

  (**
Just like [intR] defines the memory representation for the type [int],
we can define [PointR] to define the memory representation for the class [Point].
The following says, that the field x contains the integer 1 and field y contains
the integer value [5] *)

  Example PointR15 (q : cQp.t) : Rep :=
    structR "Point" q **
    _field "Point::x"  |-> intR q 1 **
    _field "Point::y"  |-> intR q 5.

(**
The above was too concrete; it stored the specific point (1, 5).
Just like [intR] takes as agument a [z : Z] to denote the mathematical number being
represented, we define a Gallina record to denote the mathematical model of what is stored:
*)

  Record Model_Point : Type :=
    { p_x : Z
    ; p_y : Z
    }.

  (** Then we can define the general class representation as follows: *)
  Definition PointR (q : cQp.t) (m : Model_Point): Rep :=
    structR "Point" q **
    _field "Point::x"  |-> intR q m.(p_x) **
    _field "Point::y"  |-> intR q m.(p_y).


  (** * Tagged Unions

   TODO: this is outdated.

   Sometimes, the interpretation of a piece of data depends on another value.
   For example, consider the following class.

   [[
   struct tagged {
     bool tag;
     union { int x; bool y; };
   };
   ]]

   A datatype like this represents *either* an integer, or a boolean.
   Following the same pattern above, we construct a Coq type to capture this.
   In this case, rather than writing a [Record], we use a [Variant].
 *)
  Variant M : Set :=
  | AnInt (_ : Z) (* a value of type [Z] *)
  | ABool (_: bool) (* a value of type [bool] *).

  (** this has both integers and booleans *)
  (*Check AnInt 3 : M.*)
  (*Check ABool true : M.*)

  (** these are tagged in Coq, i.e. we can pattern match on a value of
      type [M] to determine which case it is.
   *)
  Definition is_an_int (m : M) : bool :=
    match m with
    | AnInt _ => true
    | _ => false
    end.

  (** to write a representation predicate for a tagged union, we
      can pattern match on the model to comput the value of the [tag]
      field for the representation predicate.
   *)
  Parameters tag_field x_field y_field : field.

  Definition taggedR (m : M) : Rep :=
    structR "tagged" 1$m **
    match m with
    | AnInt z => _field tag_field |-> boolR 1$m true **
                 _field x_field |-> intR 1$m z
    | ABool b => _field tag_field |-> boolR 1$m false **
                 _field y_field |-> boolR 1$m b
    end.
  (** note that in this definition, the [x_field] and [y_field] are *not*
      disjoint.

      an equivalent way to write this definition is the following.
   *)
  Definition taggedR' (m : M) : Rep :=
    structR "tagged" 1$m **
    _field tag_field |-> boolR 1$m (is_an_int m) **
    match m with
    | AnInt z => _field x_field |-> intR 1$m z
    | ABool b => _field y_field |-> boolR 1$m b
    end.
  (** a benefit to this approach is that is is clear that, regardless of the
      value of the model, it is always safe to access the [tag] field.

      in practice, however, it isn't difficult to prove that they are equivalent.
   *)
  Goal forall (this : ptr) m, this |-> taggedR m -|- this |-> taggedR' m.
  Proof.
    intros.
    rewrite /taggedR /taggedR'.

    Succeed solve [ (* confirm the following script concludes the proof. *)
      iSplit; (* prove each direction of the entailment separately (our automation
               can only prove one direction at a time) *)
      destruct m; (* case analysis on the [m] to determine if it is an [AnInt]
                     or an [ABool] *)
      simpl; eauto with iFrame (* standard entailment checking *)
    ].

    (* This specific proof can be even easier! *)
    destruct m; (* case analysis on the [m] to determine if it is an [AnInt]
                    or an [ABool] *)
      done.
  Qed.


  (** with the above representation predicate, we can represent an object
      carrying the value [5] and an object carrying the value [false] as
      below.
   *)
  Definition __ (this : ptr) : mpred := this |-> taggedR (AnInt 5).
  Definition __1 (this : ptr) : mpred := this |-> taggedR (ABool false).

  (** one issue with the above definitions is that they do not capture the
      possible "slack" bits in the implementation. to understand the intricacies
      connected to "slack" bits, see slack_bits.v
   *)

  (** * Untagged Unions

    Untagged unions are a little bit more complex. In practice, they should
    be avoided when possible, but this doesn't always lead to nice code,
    so we do support them.

    If you must use them, we write a representation predicate for each of the
    possibilites of the [union] and then prove equivalences between them.
    Concretely, here is an example:

    [[
    union OrBytes {
      int32 word;
      struct { int16 high; int16 low; };
    };
    ]]

    The representation for [word] is easy, the one for the struct is only
    slightly more complex.
   *)
  Parameters word_field high_field low_field : field.

  Definition OrBytes_wordR (q : cQp.t) (w : Z) : Rep :=
    _field word_field |-> intR q w.

  Definition OrBytes_high_lowR (q : cQp.t) (h l : Z) : Rep :=
    _field high_field |-> intR q h **
    _field low_field |-> intR q l.

  (** Now, when we write the representation predidate for [OrBytes], we pick
      one of the two representations as primary. Here, we will pick
      [OrBytes_wordR] as primary.
   *)
  Definition OrBytesR (q : cQp.t) (w : Z) : Rep :=
    OrBytes_wordR q w.

  (** It is undefined behavior in C++ to read the element of a union that was
      not most recently written.

      To convert from one representation to another by writing, you can first
      convert the representation back to [uninitR "OrBytes" 1], and then
      re-initialize the desired union member.
   *)

  (**
     Some compilers implement a language extension which defines this behavior.
     If you wish to rely on this behavior, you can write lemmas similar to the
     following.

     This theorem allows you to view an [OrBytesR] as an [OrBytes_high_lowR]
   *)
  Lemma words_high_low : forall q w,
      OrBytesR q w -|- OrBytes_high_lowR q (Z.shiftr w 16) (Z.land w (2 ^ 16 - 1)).
  Proof. Admitted.

  (** this theorem allows you to go the other way *)
  Lemma high_low_words : forall q l h,
      OrBytes_high_lowR q l h -|- OrBytesR q (Z.lor (Z.shiftl h 16) l).
  Proof. Admitted.

  (** proving these lemmas tends to not be very difficult in most cases,
      assuming the appropriate axioms about memory layout and alignedness.
      Bare in mind that these sometimes have compiler or architecture specified
      behavior. For example, the struct above is relying on a particular
      endianness, switching to another architecture might get you the opposite
      values.
   *)

End with_Σ.
