(* A lens, to see better.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)

From elpi Require Import elpi.
From elpi.apps Require Import derive.
From elpi.apps Require Import derive.lens.

Require Import Lens.Lens.

Register Build_Lens as elpi.derive.lens.make.
Register set as elpi.derive.lens.set.
Register view as elpi.derive.lens.view.

Require Import stdpp.numbers.
#[verbose,only(lens)] derive Record State : Set := MkState
  { value : N
  }.
Print State._value.
About lens.Lens.

(* #[only(lens)] derive State. *)
Print Module State.
Import State.
Print Module State.
