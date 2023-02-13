(*
 * Copyright (c) 2022,2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export Lens.Lens.
Require Import stdpp.list.
Require Import bedrock.prelude.list_numbers.

Definition _default {A B : Type} (default : B) : Lens.Lens A A B B :=
  {| Lens.view := fun _ => default
   ; Lens.over := fun _ x => x |}.

Definition _nth {E} (n : N) : Lens.Lens (list E) (list E) (option E) E := {|
  Lens.view := (fun l => l !! n) ;
  Lens.over := (fun (f : option E -> E) (l : list E) =>
    match l !! n with
    | Some e => <[n := f (Some e)]> l
    | None => l
    end)
|}.
