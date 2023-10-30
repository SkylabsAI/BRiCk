(*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import stdpp.fin_maps.
Require Import stdpp.option.
Require Import bedrock.prelude.bytestring.

Inductive node {R V : Type} := {
  value : option V;
  k00 : option R;
  (*...*)
  kff : option R;
}.
Arguments node : clear implicits.

Definition node_get {R V : Type}
    (k : Byte.byte) (n : node R V) : option R :=
  match k with
  | Byte.x00 => n.(k00)
  (*...*)
  | Byte.xff => n.(kff)
  | _ => None
  end.

Definition node_update {R1 R2 V1 V2 : Type}
    (fr : Byte.byte -> option R1 -> option R2) (fv : option V1 -> option V2)
    (n : node R1 V1) : node R2 V2 := {|
  value := fv n.(value);
  k00 := fr Byte.x00 n.(k00);
  (*...*)
  kff := fr Byte.xff n.(kff);
|}.

Definition node_update_value {R V1 V2 : Type}
    (f : option V1 -> option V2) (n : node R V1) : node R V2 :=
  node_update (fun _ o => o) f n.

Definition node_update_child {R V : Type}
    (b : Byte.byte) (f : option R -> option R) (n : node R V) : node R V :=
  node_update (fun k o => if Byte.eqb b k then f o else o) (fun o => o) n.

Definition node_map {R1 R2 V1 V2 : Type}
    (fr : R1 -> R2) (fv : V1 -> V2) (n : @node R1 V1) : @node R2 V2 :=
  node_update (fun _ o => fr <$> o) (fun o => fv <$> o) n.

Definition node_mapi {R1 R2 V1 V2 : Type}
    (fr : Byte.byte -> R1 -> R2) (fv : V1 -> V2) (n : @node R1 V1) : @node R2 V2 :=
  node_update (fun b o => fr b <$> o) (fun o => fv <$> o) n.

Inductive bs_map (V : Type) :=
  | BSMEmpty : bs_map V
  | BSMShortcut : BS.t -> V -> bs_map V
  | BSMNode : node (bs_map V) V -> bs_map V.
Arguments BSMEmpty {_}.
Arguments BSMShortcut {_} _ _.
Arguments BSMNode {_} _.

Fixpoint bs_map_map {V1 V2 : Type} (f : V1 -> V2) (m : bs_map V1) : bs_map V2 :=
  match m with
  | BSMEmpty => BSMEmpty
  | BSMShortcut suffix v => BSMShortcut suffix (f v)
  | BSMNode n => BSMNode (node_map (bs_map_map f) f n)
  end.

Fixpoint bs_map_find {V : Type}
    (k : BS.t) (m : bs_map V) {struct k} : option V :=
  match m with
  | BSMEmpty => None
  | BSMShortcut s v => if BS.eqb k s then Some v else None
  | BSMNode n =>
    match k with
    | BS.EmptyString => n.(value)
    | BS.String b k =>
      match node_get b n with
      | None => None
      | Some m => bs_map_find k m
      end
    end
  end.

Fixpoint shrink {V : Type} (m : bs_map V) : bs_map V :=
  match m with
  | BSMEmpty => m
  | BSMShortcut _ _ => m
  | BSMNode n =>
    let n := node_map shrink id n in
    BSMEmpty
  end.

(*
Fixpoint bs_map_update {V : Type}
    (f : option V → option V) (k : bs) (m : bs_map V) {struct k} : bs_map V :=
  match m with
  | BSMEmpty =>
    match f None with
    | None => BSMEmpty
    | Some v => BSMShortcut k v
    end
  | BSMShortcut s v =>
    match f (if BS.eqb k s then Some v else None) with
    | None => BSMEmpty
    | Some v => BSMShortcut k v
    end
  | BSMNode n =>
    match k with
    | BS.EmptyString =>
      BSMNode (node_update_value f n)
    | BS.String b k =>
      let update o :=
        match o with
        | None =>
          match f None with
          | None => None
          | Some v => BSMShortcut k v
          end
        | Some m =>
          Some (bs_map_update )
            BSMShortcut

      in
      BSMNode (node_update_child b update n)
    end
  end.
*)


#[global] Instance bs_map_fmap : FMap bs_map := @bs_map_map.
#[global] Instance bs_map_lookup (V : Type) : Lookup bs V (bs_map V) := bs_map_find.
#[global] Instance bs_map_empty (V : Type) : Empty (bs_map V) := BSMEmpty.
#[global] Instance bs_map_partial_alter (V : Type) : PartialAlter bs V (bs_map V). Admitted.
#[global] Instance bs_map_omap : OMap bs_map. Admitted.
#[global] Instance bs_map_merge : Merge bs_map. Admitted.
#[global] Instance bs_map_map_fold (V : Type) : MapFold bs V (bs_map V). Admitted.

#[global] Instance bs_map_finmap : FinMap BS.t bs_map. Admitted.
