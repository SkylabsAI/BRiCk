(*
 * Copyright (C) BedRock Systems Inc. 2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
(**
 * Logical interpretation of object lifetime
 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNatDef.

From bedrock.lang.cpp Require Import ast semantics.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred
     translation_unit.

Section with_cpp.
  Context `{Σ : cpp_logic} {σ : genv}.

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
  (* wrap up [pred.vtable] as a [Rep] *)
  Definition _vtable (q : Qp) (mp : gmap obj_name (ptr * list globname)) : Rep :=
    {| monPred_at p := vtable mp q p |}.

  Require Import bedrock.avl.

  Definition patch := IM.t ptr.
  Definition vt := list (obj_name * (ptr * list globname)).
  Definition off := list globname.

  (* this makes a vtable for a [Struct] treating it as the most derived class
   *)
  Definition make_vtable (σ : genv) (virt : list (obj_name * option obj_name))
    : option vt :=
    mapM (M:=option) (fun '(k,v) =>
            match v with
            | None => Some (k,(nullptr, nil))
            | Some nm =>
              match glob_addr σ nm with
              | None => None
              | Some p => Some (k, (p, nil))
              end
            end) virt.

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
                          match List.find (fun '(nm',_) => if decide (nm = nm') then true else false) here_over with
                          | None => over
                          | Some (l,_) => <[ l := to.1 ]> over
                          end)
                       | None => ((nm, to) :: acc, over)
                       end) (nil, over) mp).
  Defined.

  Eval compute in fun p =>
    update_vtable {[ "a"%bs := p ]} ("z"%bs::nil) nil (("a"%bs, (nullptr, nil)) :: nil).

  (** this definition of [vtable] provides abstraction *)
  Definition vtable_def (q : Qp)
             (s : gmap obj_name (thread_info -> list val -> (val -> epred) -> mpred))
    : Rep :=
    as_Rep (fun this => Exists fps, (* abstraction *is* existential quantification *)
      _at (_eq this) (_vtable q fps) **
      [∗map] n ↦ ps ∈ merge (fun a b => match a , b with
                                     | Some a , Some b => Some (a,b)
                                     | _ , _ => None
                                     end) fps s ,
      □ (Forall ti vs Q, snd ps ti vs Q -* fspec ti (Vptr (fst ps)) vs Q)).
  Definition vtable_aux : seal (@vtable_def). by eexists. Qed.
  Definition vtable := vtable_aux.(unseal).
  Definition vtable_eq : @vtable = _ := vtable_aux.(seal_eq).
