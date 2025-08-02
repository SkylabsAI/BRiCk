(*
 * Copyright (c) 2024-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import Stdlib.Structures.OrderedTypeAlt.
Require Import Stdlib.FSets.FMapAVL.
Require Import bluerock.prelude.avl.
Require Import bluerock.prelude.compare.
Require Import bluerock.lang.cpp.syntax.prelude.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.compare.

(** ** Name maps *)

#[global] Declare Instance name_comparison :
  Comparison (compareN).	(** TODO *)

Module internal.
  Module AtomicNameMap.
    Module Compare.
      Definition t : Type := atomic_name.
      #[local] Definition compare : t -> t -> comparison := atomic_name_compare.
      #[local] Infix "?=" := compare.
      #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
      Proof. Admitted.
      #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
      Proof. Admitted. (*exact: base.compare_trans. Qed. *)
    End Compare.
    Module Key := OrderedType_from_Alt Compare.
    Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
    Proof. apply LeibnizComparison.cmp_eq; refine _. Admitted. (*Qed. *)
    Include FMapAVL.Make Key.
    Include FMapExtra.MIXIN Key.
    Include FMapExtra.MIXIN_LEIBNIZ Key.

    Definition ix {V} (k : Compare.t) : Lens (t V) (t V) (option V) (option V) :=
      {| Lens.view := find k
       ; Lens.over f m :=
            let v := find k m in
            match f v with
            | None => match v with
                     | None => m
                     | Some _ => remove k m
                     end
            | Some v => add k v m
            end
      |}.

    Definition raw_ix {V} (k : Compare.t) : Lens (Raw.t V) (Raw.t V) (option V) (option V) :=
      {| Lens.view := Raw.find k
      ; Lens.over f m :=
          let v := Raw.find k m in
          match f v with
          | None => match v with
                    | None => m
                    | Some _ => Raw.remove k m
                    end
          | Some v => Raw.add k v m
          end
      |}.

  End AtomicNameMap.

  Module TempArgMap.
    Module Compare.
      Definition t : Type := list temp_arg'.
      #[local] Definition compare : t -> t -> comparison :=
        List.compare (temp_arg.compare compareN compareT compareE).
      #[local] Infix "?=" := compare.
      #[local] Lemma compare_sym x y : (y ?= x) = CompOpp (x ?= y).
      Proof. Admitted.
      #[local] Lemma compare_trans c x y z : (x ?= y) = c -> (y ?= z) = c -> (x ?= z) = c.
      Proof. Admitted. (*exact: base.compare_trans. Qed. *)
    End Compare.
    Module Key := OrderedType_from_Alt Compare.
    Lemma eqL : forall a b, Key.eq a b -> @eq _ a b.
    Proof. apply LeibnizComparison.cmp_eq; refine _. Admitted. (*Qed. *)
    Include FMapAVL.Make Key.
    Include FMapExtra.MIXIN Key.
    Include FMapExtra.MIXIN_LEIBNIZ Key.

    Definition ix {V} (k : Compare.t) : Lens (t V) (t V) (option V) (option V) :=
      {| Lens.view := find k
      ; Lens.over f m :=
          let v := find k m in
          match f v with
          | None => match v with
                    | None => m
                    | Some _ => remove k m
                    end
          | Some v => insert k v m
          end
      |}.

    Definition raw_ix {V} (k : Compare.t) : Lens (Raw.t V) (Raw.t V) (option V) (option V) :=
      {| Lens.view := Raw.find k
      ; Lens.over f m :=
          let v := Raw.find k m in
          match f v with
          | None => match v with
                    | None => m
                    | Some _ => Raw.remove k m
                    end
          | Some v => Raw.add k v m
          end
      |}.

  End TempArgMap.

End internal.

Module NameMap.
  Import internal.

  Section with_elt.
    Context {elt : Type}.

    Inductive t : Type :=
    | Branch (here : AtomicNameMap.Raw.t t)
            (scoped : AtomicNameMap.Raw.t t)
            (inst : TempArgMap.Raw.t t)
            (v : option elt)
    | Leaf (value : elt).

    Definition here (m : t) : _ :=
      match m with
      | Branch here _ _ _ => here
      | Leaf _ => ∅
      end.
    Definition scoped (m : t) : _ :=
      match m with
      | Branch _ scoped _ _ => scoped
      | Leaf _ => ∅
      end.
    Definition inst (m : t) : _ :=
      match m with
      | Branch _ _ inst _ => inst
      | Leaf _ => ∅
      end.
    Definition value (m : t) : option elt :=
      match m with
      | Branch _ _ _ v => v
      | Leaf v => Some v
      end.
    Definition branch := Branch.
    #[local] Instance atomic_name_eq_dec : EqDecision atomic_name :=
      LeibnizComparison.from_comparison.
    Instance t_empty : Empty t := branch ∅ ∅ ∅ None.

    Fixpoint find_map (n : name) (m : t) : option t :=
      match n with
      | Nglobal an => here m !! an
      | Nscoped n an => find_map n m ≫= fun m => scoped m !! an
      | Ninst n i => find_map n m ≫= fun m => inst m !! i
      | _ => None
      end.
    Definition find (n : name) (m : t) : option elt :=
      find_map n m ≫= value.

    #[local] Fixpoint ix_over_aux (n : name) (f : option t -> option t)
      (m : t) : t :=
      match n with
      | Nglobal an =>
          let here := here m &: AtomicNameMap.raw_ix an %= f in
          branch here (scoped m) (inst m) (value m)
      | Nscoped n an =>
          let f om : option t :=
            match om with
            | None => match f None with
                     | None => None
                     | Some v => Some $ branch ∅ (∅ &: AtomicNameMap.raw_ix an .= Some v) ∅ None
                     end
            | Some m =>
                let scoped := scoped m &: AtomicNameMap.raw_ix an %= fun om => f om in
                Some $ branch (here m) scoped (inst m) (value m)
            end
          in
          ix_over_aux n f m
      | Ninst n i =>
          let f om : option t :=
            match om with
            | None => match f None with
                      | None => None
                      | Some v => Some $ branch ∅ ∅ (∅ &: TempArgMap.raw_ix i .= Some v) None
                      end
            | Some m =>
                let inst := inst m &: TempArgMap.raw_ix i %= fun om => f om in
                Some $ branch (here m) (scoped m) inst (value m)
            end
          in
          ix_over_aux n f m
      | _ => m
      end%lens.
    #[local]
    Definition ix_over (n : name) (f : option elt -> option elt) : t -> t :=
      let f om : option t :=
        match om with
        | None => match f None with
                 | None => None
                 | Some v => Some $ Leaf v
                 end
        | Some b =>
            Some $ branch (here b) (scoped b) (inst b) (f (value b))
        end
      in
      ix_over_aux n f.

    Definition ix (n : name) : Lens t t (option elt) (option elt) :=
      {| Lens.view m := find n m ; Lens.over f m := ix_over n f m |}.

    Definition insert (n : name) (v : elt) (m : t) : t :=
      Lens.over (ix n) (fun _ => Some v) m.
    Definition remove (n : name) (m : t) : t :=
      Lens.over (ix n) (fun _ => None) m.
  End with_elt.
  #[global] Arguments t _ : clear implicits.

  (* Test case *)
  (* Eval vm_compute in *)
  (*   let a := Nglobal $ Nid "a" in *)
  (*   let ab := Nscoped a $ Nid "b" in *)
  (*   let abc := Nscoped ab $ Nid "c" in *)
  (*   let abd := Nscoped ab $ Nid "d" in *)
  (*   insert a 1 $ insert abc 2 $ insert abd 3 $ ∅. *)

End NameMap.

Module NM.
  Include NameMap.
End NM.

Module TM.
  Include NameMap.
End TM.
