(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * Logical interpretation of object lifetime
 *)
Require Import Coq.Lists.List.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred.

  Require Import bedrock.lang.cpp.heap_notations.
  Local Open Scope bs_scope.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

  (* wrap up [pred.vtable] as a [Rep] *)
  (* note: [list globname] is problematic because i don't know where to
   * start from. i can make this an [Offset], or i can simply add a [globname]
   * for the starting class....
   *)
  Definition _vtable (q : Qp) (mp : list (obj_name * (ptr * Offset))) : Rep.
    (* {| monPred_at p := vtable _ q p |}. *)
  Admitted.

  (** this function computes a separation logic assertion that
    patches the virtual table of base classes with methods that have been
    overridden by this class.

    note that the update is deep in the sense that it might need to patch
    ancestors and not just direct parents.
    - the alternative is to make them shallow and contain forwarding pointers.
      this would simplify some of the meta-theory, but it would complicate the
      proofs because in order to dispatch you need partial ownership of many
      tables.

    note: because we don't have a well-foundedness condition on our environment,
    we use fuel to make this terminating. in practice this isn't a problem
    because the depth of the inheritence tree is bounded by the number of
    classes in the environment.
   *)

  (** * virtual function tables *)

  Require Import bedrock.avl.

  Definition patch := IM.t ptr.
  Definition vt := list (obj_name * (ptr * Offset)).
  Definition off := Offset.

  (* this patches a single vtable that already exists in memory.
   * [here_over] is the overrides of this class (which need to
   * be subsequently overidden in higher classes)
   *)
  Definition update_vtable (over : patch) (offset : off)
             (here_over : list (obj_name * obj_name))
             (* this is the overrides from the struct definition *)
    : vt -> vt * patch.
  refine (fun mp =>
    List.fold_right (fun '(nm, to) '(acc,over) =>
                       match over !! nm with
                       | Some to' =>
                         ((nm, (to', offset)) :: acc,
                          match List.find (fun '(_, nm') => if decide (nm = nm') then true else false) here_over with
                          | None => over
                          | Some (l,_) => <[ l := to' ]> over
                          end)
                       | None => ((nm, to) :: acc, over)
                       end) (nil, over) mp).
  Defined.

  Eval compute in fun p =>
    update_vtable {[ "a"%bs := p ]} (_id) nil (("a"%bs, (nullptr, _id)) :: nil).

  Fixpoint patch_vtables (fuel : nat) (this : Loc) (cls : globname) (o : off) (p : patch) (Q : mpred) {struct fuel} : mpred.
  refine
    match fuel with
    | O => lfalse
    | S fuel =>
      match σ.(genv_tu) !! cls with
      | Some (Gstruct st) =>
        Exists v, _at this (_vtable 1 v) **
                (let '(v',p') := update_vtable p o st.(s_overrides) v in
                 _at this (_vtable 1 v') -*
                     List.fold_right (fun '(cls',_) Q => patch_vtables fuel (_offsetL (_base σ cls cls') this) cls' (_dot o (_derived σ cls' cls)) p' Q) Q st.(s_bases))
      | _ => lfalse
      end
    end.
  Defined.

  (* this makes a vtable for a [Struct] treating it as the most derived class
   *)
  Definition make_vtable (s : Struct) : option vt :=
    match s with
    | {| s_virtuals := virt |} =>
    mapM (M:=option) (fun '(k,v) =>
            match v with
            | None => Some (k,(nullptr, _id))
            | Some nm =>
              match glob_addr σ nm with
              | None => None
              | Some p => Some (k, (p, _id))
              end
            end) virt
    end.

  Definition lifetime_begin (this : Loc) (cls : globname) (Q : mpred) : mpred.
  refine
    match σ.(genv_tu) !! cls with
    | Some (Gstruct s) =>
    match make_vtable s with
    | Some v =>
      match mapM _ s.(s_overrides) with
      | Some over =>
        let over := list_to_map over in
      this |-> _vtable 1 v -*
      List.fold_right (fun '(cls',_) Q =>
                         patch_vtables 100 (this ., _base σ cls cls') cls'
                                       (_derived σ cls' cls) over Q) Q s.(s_bases)
      | None => lfalse
      end
    | _ => lfalse
    end
    | _ => lfalse
    end.
  refine (fun '(f,o) =>
            match List.find (fun '(nm',_) => if decide (o = nm') then true else false) v with
            | Some (_,(p,_)) => Some (f, p)
            | None => None
            end).
  Defined.

  Definition lifetime_end (this : Loc) (cls : globname) (Q : mpred) : mpred.
    

End with_cpp.

  Require Import bedrock.lang.cpp.parser.
Definition module : translation_unit := 
  Eval reduce_translation_unit in parser.decls (
    (Dstruct "_Z1A" (Some
        {| s_bases := (nil)
         ; s_fields :=
          (nil)

         ; s_layout := Unspecified
         ; s_size := 8
         ; s_virtuals := mk_virtuals
          (("_ZNK1A3fooEv", None) :: ("_ZN1AD0Ev",
            (Some "_ZN1AD0Ev")) :: nil)
           ; s_overrides := mk_overrides
            (nil)
           ; s_virtual_dtor :=
          (Some "_ZN1AD0Ev")|})) ::
      (Dstruct "_Z1B" (Some
          {| s_bases := (("_Z1A", {| li_offset :=0|}) :: nil)
           ; s_fields :=
            (nil)

           ; s_layout := Unspecified
           ; s_size := 8
           ; s_virtuals := mk_virtuals
            (("_ZN1BD0Ev",
              (Some "_ZN1BD0Ev")) :: nil)
             ; s_overrides := mk_overrides
              (("_ZN1AD0Ev", "_ZN1BD0Ev") :: nil)
             ; s_virtual_dtor :=
            (Some "_ZN1BD0Ev")|})) ::
        (Dstruct "_Z1C" (Some
            {| s_bases := (("_Z1B", {| li_offset :=0|}) :: nil)
             ; s_fields :=
              (nil)

             ; s_layout := Unspecified
             ; s_size := 8
             ; s_virtuals := mk_virtuals
              (("_ZNK1C3fooEv",
                (Some "_ZNK1C3fooEv")) :: ("_ZN1CD0Ev",
                (Some "_ZN1CD0Ev")) :: nil)
               ; s_overrides := mk_overrides
                (("_ZNK1A3fooEv", "_ZNK1C3fooEv") :: ("_ZN1BD0Ev", "_ZN1CD0Ev") :: nil)
               ; s_virtual_dtor :=
              (Some "_ZN1CD0Ev")|}))
        :: nil)%bs.

  Eval compute in fun p => make_vtable (σ:={| genv_tu := module ; glob_addr := fun f => Some (p f) ; pointer_size := 8 |})
  ({| s_bases := (("_Z1B", {| li_offset :=0|}) :: nil)
             ; s_fields :=
              (nil)

             ; s_layout := Unspecified
             ; s_size := 8
             ; s_virtuals := mk_virtuals
              (("_ZNK1C3fooEv",
                (Some "_ZNK1C3fooEv")) :: ("_ZN1CD0Ev",
                (Some "_ZN1CD0Ev")) :: nil)
               ; s_overrides := mk_overrides
                (("_ZNK1A3fooEv", "_ZNK1C3fooEv") :: ("_ZN1BD0Ev", "_ZN1CD0Ev") :: nil)
               ; s_virtual_dtor :=
              (Some "_ZN1CD0Ev")|})%bs.


  Goal forall `{Σ : cpp_logic} (this : Loc) p Q,
      let σ := {| genv_tu := module ; glob_addr := fun f => Some (p f) ; pointer_size := 8 |} in
      let c := this in
      let b := c ., _base σ "_Z1C" "_Z1B" in
      let a := b ., _base σ "_Z1B" "_Z1A" in
      |-- lifetime_begin a "_Z1A" (lifetime_begin b "_Z1B" (lifetime_begin c "_Z1C" Q)).
    intros.
    Require Import iris.proofmode.tactics.
    (* unfold lifetime_begin; simpl. *)
    iIntros "A".
    simpl.
    iIntros "B".
    simpl.
    iExists _. iSplitL "A"; [ iAssumption | ].
    simpl.
    iIntros "A".
    iIntros "C".
    simpl.
    iExists _. iSplitL "B"; [ iAssumption | ].
    simpl. iIntros "B".
    iExists _. iSplitL "A"; [ iAssumption | ].
    simpl.
    iIntros "A".

    A : B, C
    B : virtual X
    C : X


  Require Import bedrock.lang.cpp.logic.wp.

  Fixpoint to_path (ls : list globname) (g : globname) (loc : Loc) : Loc :=
    match ls with
    | nil => loc
    | l :: ls =>
      to_path ls l (_offsetL (_derived σ g l) loc)
    end.





  (** this definition of [vtable] provides abstraction *)
  Definition vtable_def (q : Qp)
             (s : list (obj_name * (thread_info -> list val -> (val -> epred) -> mpred)))
    : Rep.
  refine (
    as_Rep (fun this => Exists fps, (* abstraction *is* existential quantification *)
      _at (_eq this) (_vtable q fps) **
      [∗list] ps ∈ combine fps s,
        let '((nm, (p,off)), (_, PQ)) := ps in
        □ (Forall this ti vs Q,
             PQ ti (Vptr this :: vs) Q -*
             Exists this', to_path off _ (_eq this) &~ this' **
             fspec ti (Vptr p) (Vptr this :: vs) Q))).
     (** can this be dependent on σ? possibly because it won't matter what the
         σ actually is.
      *)
  refine "???"%bs. (* todo: what do i fill in here? *)
  Defined.

  Definition vtable_aux : seal (@vtable_def). by eexists. Qed.
  Definition vtable := vtable_aux.(unseal).
  Definition vtable_eq : @vtable = _ := vtable_aux.(seal_eq).


End with_cpp.

