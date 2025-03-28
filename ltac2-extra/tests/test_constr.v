(*
 * Copyright (C) 2021-2024 BlueRock Security, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source
 * License. See the LICENSE-BedRock file in the repository root for details.
 *)

Require Import bluerock.ltac2.extra.internal.init.
Require Import bluerock.ltac2.extra.internal.constr.

Module ConstrSet_test.
  Import Ltac2.
  Import Constr.ConstrSet.

  (* Make sure that all operations on [ConstrSet] work on 0, 1, and many goals
     even when the goals are not currently focussed. *)
  Ltac2 test_multi_goal tac :=
    let t := 'True in
    let f := 'False in
    split; tac t f.

  Goal True /\ True.
   Succeed test_multi_goal (fun _ _ =>
     let _ := empty in ()
   ).
   Succeed test_multi_goal (fun _ _ =>
     if is_empty empty then () else fail
   ).
   Succeed test_multi_goal (fun _ _ =>
     if is_empty (diff empty empty) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     let _ := of_list [t; f] in ()
   ).
   Succeed test_multi_goal (fun t f =>
     if mem t (of_list [t; f]) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     if mem f (of_list [t; f]) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     if mem f (diff (of_list [t; f]) (of_list [f])) then fail else ()
   ).
   Succeed test_multi_goal (fun t f =>
     if mem t (diff (of_list [t; f]) (of_list [f])) then () else fail
   ).
   Succeed test_multi_goal (fun t f =>
     let _ :=
       let l := elements (diff (of_list [t; f]) (of_list [f])) in
       (if List.mem Constr.equal t l then () else fail);
       (if List.mem Constr.equal f l then fail else ())
     in ()
   ).
  Abort.
End ConstrSet_test.

Module DecomposeProj_Tests.
  Import Ltac2.
  Import Constr.Unsafe.Destruct.

  Ltac2 test t :=
    match of_projection t with
    | Some _ => exact I
    | _ => Control.throw (Invalid_argument None)
    end.

  Module NonPrim.
    Record test {n: nat} := TEST { m: nat; H: m=n }.
    Notation t :=
      ltac:(let t := constr:((TEST 1 1 eq_refl).(H)) in exact t)
      (only parsing).
    Goal True. test 't. Qed.
  End NonPrim.

  Module Prim.
    #[projections(primitive)]
    Record test {n: nat} := TEST { m: nat; H: m=n }.
    Notation t1 :=
      ltac:(let t := eval lazy delta [H] in (TEST 1 1 eq_refl).(H) in exact t)
      (only parsing).
    Goal True. test 't1. Qed.

    Notation t2 :=
      ltac:(let t := constr:((TEST 1 1 eq_refl).(H)) in exact t)
      (only parsing).
    Goal True. test 't2. Qed.
  End Prim.
End DecomposeProj_Tests.


Module Vars_Test.
  Import Ltac2.
  Import printf.Printf.

  #[projections(primitive)]
  Record ty (u : unit) := R { f : unit }.

  Lemma test u (r : ty u) : @f u r = tt.
  Proof.
    intros.
    Control.enter (fun () =>
      let g := Control.goal () in
      let v := Constr.Vars.vars_really_needed g in
      Control.assert_true (FSet.mem @u v)
    ).
  Abort.

End Vars_Test.


Module Evar_Test.
  Import Ltac2 Ltac2.Bool Constr Unsafe Printf.

  Require Import bluerock.ltac2.extra.internal.level_env.


  Ltac2 add_exists (env : LevelEnv.t) (c : constr) : constr :=
    let folder (decl : LevelEnv.rel_decl) (acc : constr) : constr :=
      match decl with
      | Constr.Unsafe.RelDecl.Assum b =>
          let ty := Binder.type b in
          let p := make_lambda b acc in
          Constr.Unsafe.make_app2 '@ex ty p
      | Constr.Unsafe.RelDecl.Def _ _ => Control.throw (Invalid_argument None)
      end
    in
    let decls := LevelEnv.to_list env in
    let c := LevelEnv.level_subst env c in
    let c := List.fold_right folder decls c in
    c.

  Ltac2 evar_to_eqns (e : evar) (inst : constr array) : constr :=
    let ctx := Evar.context e in
    (* Var set of [ctx] *)
    let ctx_vars :=
      let fn s (id,_,_) := FSet.add id s in
      List.fold_left fn (FSet.empty FSet.Tags.ident_tag) ctx
    in
    (* Var set of instance *)
    let inst_vars :=
      let fn s c := FSet.union (Vars.vars_really_needed c) s in
      Array.fold_left fn (FSet.empty FSet.Tags.ident_tag) inst
    in
    let hyps := Control.hyps () in
    (* (* Var set of current goal *) *)
    (* let goal_vars := *)
    (*   let fn s (id,_,_) := FSet.add id s in *)
    (*   List.fold_left fn (FSet.empty FSet.Tags.ident_tag) hyps *)
    (* in *)
    let new_vars := FSet.diff inst_vars ctx_vars in
    (* disappeared variables *)
    (* let dis_vars := FSet.diff ctx_vars goal_vars in *)
    (* Reverse [inst] to be in the same order as [ctx] *)
    let inst := List.rev (Array.to_list inst) in
    let combined := List.combine ctx inst in
    (* Compute all items in [inst] of the form [orig_id := new_id] and compute a
       map from [new_id] to [old_id]. Using [old_id] in place of [new_id] will
       allows us to avoid introducing an existential quantifier for [new_id].
       This map is not unique. *)
    let new_to_old :=
      let fn ((orig_id, _, _), val) :=
        match kind val with
        | Var new_id => if Ident.equal orig_id new_id then None else Some (orig_id, new_id)
        | _ => None
        end
      in
      let ids := List.map_filter fn combined in
      let emp := FMap.empty FSet.Tags.ident_tag in
      List.fold_left (fun m (old, new) => FMap.add new old m) emp ids
    in
    (* We will need existential quantifiers for all new variables that cannot be
       directly translated into old variables. If the new variables have bodies,
       we need equations for those as well.
       TODO: we could try to inline variables with bodies but that is more complicated.
     *)
    let (ex_lenv, extra_eqs) :=
      let fn ((lenv, extra_eqs) as acc) (id, oval, ty) :=
        if FSet.mem id new_vars && neg (FMap.mem id new_to_old) then
          let lenv := LevelEnv.add_decl lenv (RelDecl.Assum (Binder.make (Some id) ty)) in
          let extra_eqs :=
            match oval with
            | Some val => let lhs := make_var id in constr:($lhs = $val) :: extra_eqs
            | None => extra_eqs
            end
          in
          (lenv, extra_eqs)
        else
          acc
      in
      (* We go through [Control.hyps] to get everything in the correct order. *)
      List.fold_left fn (LevelEnv.empty, []) hyps
    in
    (* Create equations for [inst]. *)
    let eqs :=
      let fn eqs ((orig_id, _, ty), val) :=
        let lhs := make_var orig_id in
        match kind val with
        | Var new_id =>
            (* skip [a = a] *)
            if Ident.equal orig_id new_id then
              eqs
            (* skip [old = new] mappings *)
            else
              match FMap.find_opt new_id new_to_old with
              | Some old_id' => if Ident.equal old_id' orig_id then eqs else
                                  make_app3 '@eq ty lhs val :: eqs
              | _ => make_app3 '@eq ty lhs val :: eqs
              end
        | _ =>
            make_app3 '@eq ty lhs val :: eqs
        end
      in
      List.fold_left fn extra_eqs combined
    in
    let prop :=
      match eqs with
      | [] => 'True
      | e :: eqs =>
        List.fold_left (fun x y => constr:(and $x $y)) e eqs
      end
    in
    (* Prepare substitution for existentials *)
    let ids :=
      let fn decl ids :=
        match decl with
        | RelDecl.Assum b => Option.get (Binder.name b) :: ids
        | _ => Control.throw (Invalid_argument None)
        end
      in
      LevelEnv.foldl fn ex_lenv []
    in
    let ids := List.rev ids in
    (* We also need to substitute new variables that have been mapped to old variables. *)
    let (mapped_new_ids, mapped_old_ids) :=
      List.split (FMap.bindings new_to_old)
    in
    let mapped_old_constrs := List.map make_var mapped_old_ids in
    (* Perform both substitutions at the same time. *)
    let prop := closenl (List.append mapped_new_ids (List.rev ids)) 1 prop in
    (* printf "%t" prop; *)
    (* The first few rels now need to be replaced by the evars existing variables *)
    let prop := substnl mapped_old_constrs 0 prop in
    (* printf "%t" prop; *)
    add_exists ex_lenv prop
  .

  Ltac2 default_evar_inst e : constr array :=
    let ctx := Evar.context e in
    let ctx := List.map (fun (id, _, _) => make_var id) ctx in
    Array.of_list (List.rev ctx).

  Goal forall a b : bool, exists x : Prop, forall y z : bool, a = y -> b = negb z -> x /\ x.
  Proof.
    intros.
    (* Set Printing All. *)
    Set Printing Existential Instances.
    eexists ?[x].
    intros.
    split.
    1: {
    lazy_match! goal with
    | [ |- ?l ] =>
      match kind l with
      | Evar e inst =>
          let prop := evar_to_eqns e inst in
          printf "%t" prop
      | _ => Control.throw (Invalid_argument None)
      end
    end.
    subst a.
    subst b.
    lazy_match! goal with
    | [ |- ?l ] =>
      match kind l with
      | Evar e inst =>
          let prop := evar_to_eqns e inst in
          let inst := default_evar_inst e in
          Unification.unify TransparentState.empty (make_evar e inst) prop
      | _ => Control.throw (Invalid_argument None)
      end
    end.
    lazy_match! goal with
    | [ |- exists z', negb z = negb z' ] => ()
    end.
    eexists. reflexivity.
    }
    1: {
      clear.
      lazy_match! goal with
      | [ |- exists z, b = negb z ] => ()
      end.
      eexists (negb b). now destruct b.
    }
  Qed.

  Goal forall a b : bool, exists x : Prop, forall y, a = y -> x /\ x.
  Proof.
    intros.
    Set Printing All.
    Set Printing Existential Instances.
    eexists ?[x].
    lazy_match! goal with
    | [ |- forall y (_ : a = y), ?l /\ _ ] =>
      match kind l with
      | Evar e inst =>
          let ctx := Evar.context e in
          let ids := List.map (fun (id, _, _) => id) ctx in
          Control.assert_true (List.equal Ident.equal ids [@a; @b]);
          let inst := Array.to_list inst in
          (* printf "inst:"; *)
          (* List.iter (printf "%t") inst; *)
          let cmb := List.combine ids (List.rev inst) in
          (* printf "ids:"; *)
          (* List.iter (printf "%I") ids; *)
          Control.assert_true (List.for_all (fun (id, c) => Constr.equal (make_var id) c) cmb)
      | _ => Control.throw (Invalid_argument None)
      end
    end.
    intros.
    split.
    -
      pose (evar := ?x).
      Succeed ltac1:(rename a into c).
      Fail ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(?x) constr:(?x).
      Succeed ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(evar) constr:(evar).
      Succeed ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(?x@{a:=c;b:=b}) constr:(?x@{a:=c;b:=b}).
      (* solution is interpreted using the substitution defined by the instance *)
      Fail ltac1:(rename a into c); ltac1:(instantiate (1 := if c then True else True)).
      Succeed ltac1:(rename a into c); ltac1:(instantiate (1 := if a then True else True)).
      (* solution is _not_ interpreted through substitution *)
      Succeed ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(?x@{a:=c; b:=b}) constr:(if c then True else True).
      Succeed ltac1:(rename a into c); Unification.unify TransparentState.empty constr:(?x@{a:=negb c; b:=b}) constr:(exists c, if negb c then True else True).
      subst a.
      Succeed Unification.unify TransparentState.empty constr:(evar) constr:(evar).
      ltac1:(instantiate (1 := if a then True else True)). (* solution is interpreted using the substitution defined by the instance *)
      ltac1:(now destruct y).
    - ltac1:(now destruct a).
  Qed.

End Evar_Test.
