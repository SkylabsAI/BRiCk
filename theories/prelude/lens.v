(*
 * Copyright (c) 2022,2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Export Lens.Lens.

Definition _default {A B : Type} (default : B) : Lens.Lens A A B B :=
  {| Lens.view := fun _ => default
   ; Lens.over := fun _ x => x |}.
