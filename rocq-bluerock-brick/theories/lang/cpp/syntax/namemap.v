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
  End TempArgMap.

  Module ArrayMap.
    Section with_K.
      Context {K : Type}.
      Context {DEC : EqDecision K}.

      Definition t (T : Type) : Type :=
        list (K * T).

      Definition find {T} (m : t T) (k : K) : option T :=
        snd <$> List.find (fun kv => bool_decide (kv.1 = k)) m.

      Definition empty {T} : t T := [].

      Definition insert {T} (k : K) (v : T) (m : t T) : t T :=
        (k,v) :: m.
      Definition remove {T} (k : K) (m : t T) : t T :=
        List.filter (fun x => ~~bool_decide (x.1 = k)) m.

      Definition ix {T} (k : K) : Lens (t T) (t T) (option T) (option T) :=
        {| Lens.view m := find m k
         ; Lens.over f m :=
             match find m k with
             | None => match f None with
                      | None => m
                      | Some v => insert k v m
                      end
             | Some v => match f (Some v) with
                        | None => remove k m
                        | Some v' => insert k v' $ remove k m
                        end
             end
        |}.
      End with_K.
    Arguments t _ _ : clear implicits.

  End ArrayMap.
  #[local] Instance am_Empty {K T} : Empty (ArrayMap.t K T) :=
    ArrayMap.empty.
  #[local] Instance am_Lookup {K T} {_ : EqDecision K} : Lookup K T (ArrayMap.t K T) :=
    fun k m => ArrayMap.find m k.

  (* NOTE: this works.
  Inductive map {t : Type} : Type :=
  | Branch (here : AtomicNameMap.Raw.t (@map t))
           (scoped : AtomicNameMap.Raw.t (@map t))
           (inst : TempArgMap.Raw.t (@map t))
           (v : option t)
  | Leaf (value : t).
  Arguments map _ : clear implicits.
  *)


  Inductive map {t : Type} : Type :=
  | Branch (here : ArrayMap.t atomic_name (@map t))
           (scoped : ArrayMap.t atomic_name (@map t))
           (inst : ArrayMap.t (list temp_arg') (@map t))
           (v : option t)
  | Leaf (value : t).
  Arguments map _ : clear implicits.

  Definition here {T} (m : map T) : _ :=
    match m with
    | Branch here _ _ _ => here
    | Leaf _ => ∅
    end.
  Definition scoped {T} (m : map T) : _ :=
    match m with
    | Branch _ scoped _ _ => scoped
    | Leaf _ => ∅
    end.
  Definition inst {T} (m : map T) : _ :=
    match m with
    | Branch _ _ inst _ => inst
    | Leaf _ => ∅
    end.
  Definition value {T} (m : map T) : option T :=
    match m with
    | Branch _ _ _ v => v
    | Leaf v => Some v
    end.
  Definition branch {T} := @Branch T.
  #[local] Instance atomic_name_eq_dec : EqDecision atomic_name := LeibnizComparison.from_comparison.

  Fixpoint find_map {T} (n : name) (m : map T) : option (map T) :=
    match n with
    | Nglobal an => here m !! an
    | Nscoped n an => find_map n m ≫= fun m => scoped m !! an
    | Ninst n i => find_map n m ≫= fun m => inst m !! i
    | _ => None
    end.
  Definition find {T} (n : name) (m : map T) : option T :=
    find_map n m ≫= value.
  Instance t_empty {T} : Empty (map T) := branch ∅ ∅ ∅ None.

  Section lens.
    Context {T : Type}.
    #[local] Fixpoint ix_over_aux (n : name) (f : option (map T) -> option (map T))
      (m : map T) : map T :=
      match n with
      | Nglobal an =>
          let here := here m &: ArrayMap.ix an %= f in
          branch here (scoped m) (inst m) (value m)
      | Nscoped n an =>
          let f om : option (map T) :=
            match om with
            | None => match f None with
                     | None => None
                     | Some v => Some $ branch ∅ (∅ &: ArrayMap.ix an .= Some v) ∅ None
                     end
            | Some m =>
                let scoped := scoped m &: ArrayMap.ix an %= fun om => f om in
                Some $ branch (here m) scoped (inst m) (value m)
            end
          in
          ix_over_aux n f m
      | Ninst n i =>
          let f om : option (map T) :=
            match om with
            | None => match f None with
                      | None => None
                      | Some v => Some $ branch ∅ ∅ (∅ &: ArrayMap.ix i .= Some v) None
                      end
            | Some m =>
                let inst := inst m &: ArrayMap.ix i %= fun om => f om in
                Some $ branch (here m) (scoped m) inst (value m)
            end
          in
          ix_over_aux n f m
      | _ => m
      end%lens.
    Definition ix_over (n : name) (f : option T -> option T) : map T -> map T :=
      let f om : option (map T) :=
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

    Definition ix (n : name) : Lens (map T) (map T) (option T) (option T) :=
      {| Lens.view := find n ; Lens.over := ix_over n |}.
  End lens.

  Definition insert {T} (n : name) (v : T) (m : map T) : map T :=
    Lens.over (ix n) (fun _ => Some v) m.
  Definition remove {T} (n : name) (m : map T) : map T :=
    Lens.over (ix n) (fun _ => None) m.

  Eval vm_compute in
    let a := Nglobal $ Nid "a" in
    let ab := Nscoped a $ Nid "b" in
    let abc := Nscoped ab $ Nid "c" in
    let abd := Nscoped ab $ Nid "d" in
    insert a 1 $ insert abc 2 $ insert abd 3 $ ∅.

End internal.

Module NM.
  Include NameMap.
End NM.

Module TM.
  Include NameMap.
End TM.
