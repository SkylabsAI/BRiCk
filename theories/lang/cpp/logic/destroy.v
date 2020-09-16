(*
 * Copyright (C) BedRock Systems Inc. 2019 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Coq.ZArith.ZArith.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import
     pred wp path_pred heap_pred.
Require Import bedrock.lang.cpp.logic.dispatch.

Set Default Proof Using "Type".

Section destroy.
  Context `{Σ : cpp_logic thread_info} {σ:genv}.
  Variable (ti : thread_info).

  Local Notation _sub := (_sub (resolve:=σ)) (only parsing).
  Local Notation anyR := (anyR (resolve:=σ)) (only parsing).
  Local Notation _global := (_global (resolve:=σ)) (only parsing).

  Definition wp_dtor_pre (dtor_type : type -d> Loc -d> mpred -d> mpredI)
    : type -d> Loc -d> mpred -d> mpredI :=
    (fun t this Q =>
       match drop_qualifiers t with
       | Tnamed cls =>
         match σ.(genv_tu).(globals) !! cls with
         | Some (Gstruct st) =>
           match st.(s_dtor) with
           | DtorDeleted => False
           | DtorUser nm =>
             match σ.(genv_tu).(symbols) !! nm with
             | Some (Odestructor d) =>
               let dt := type_of_value (Odestructor d) in
               Exists da thisp, _global nm &~ da ** this &~ thisp **
                                        |> fspec σ.(genv_tu).(globals) dt ti (Vptr da) (Vptr thisp :: nil) (fun _ => Q)
             | _ => False
             end
           | DtorDefault =>
             let bases :=
                 fold_left (fun Q '(base, _) =>
                              |> dtor_type (Tnamed base) (_offsetL (_base σ cls base) this) Q) st.(s_bases) Q
             in
             fold_left (fun Q '(x,ty,_,_) =>
                          match drop_qualifiers ty with
                          | Tnamed nm =>
                            let l' := _offsetL (_field (resolve:=σ) {| f_type := cls ; f_name := x |}) this  in
                            |> dtor_type ty l' Q
                          | _ => Q
                          end) st.(s_fields) bases
           (*
            let fields := flat_map (fun '(x, ty, _, _) =>
                                      match drop_qualifiers ty with
                                      | Tnamed nm =>
                                        rec _ nm Q 
                                      | _ => nil
                                      end)%bs st.(s_fields) in
            let bases := (fun '(cls, _) => (Base cls, cls ++ "D0Ev"))%bs <$> st.(s_bases) in
            (* ^ TODO(gmm): sketchy mangling *)
            wp_dtor_impl dtor.(d_class) (Sseq nil) (List.rev (bases ++ fields)) ti args Q *)
           end
         | Some (Gunion _) => Q
         | Some (Genum t _) => |> dtor_type t this Q
         | _ => False
         end
       | _ => Q
       end)%I.

  Lemma fold_left_proper {T : ofeT} {U : Type} {n} :
    Proper ((dist n ==> pointwise_relation _ (dist n)) ==> eq ==> dist n ==> dist n) (@fold_left T U).
  Proof.
    red. red. red. red.
    induction x0; intros; subst; simpl; eauto.
    eapply IHx0; eauto.
    eapply H; eauto.
  Qed.

  Definition wp_dtor : type -> Loc -> mpred -> mpred.
    refine (fixpoint wp_dtor_pre).
    { red. red; intros.
      unfold wp_dtor_pre. red. red. red. red. red. red. red. red. red.
      intros.
      repeat match goal with
             | |- match ?X with _ => _ end ≡{_}≡ match ?X with _ => _ end =>
               destruct X; eauto
             end.
      eapply fold_left_proper; eauto.
      2:{ eapply fold_left_proper; eauto.
          red. red; intros. destruct a.
          admit. }
      2:{ eapply uPred_later_contractive.
          destruct n; eauto.
          red in H.  red. apply H. }
      { do 2 red; intros.
        destruct a as [ [[? ?] ?] ? ].
        destruct (drop_qualifiers t); eauto.
        admit. }
  Admitted.

  (* this destructs an object by invoking its destructor
     note: it does *not* free the underlying memory.
   *)
  Definition destruct_obj (cls : globname) (v : val) (Q : mpred) : mpred :=
    match σ.(genv_tu) !! cls with
    | Some (Gstruct s) =>
      match s.(s_dtor) with
      | DtorDeleted => False
      | DtorUser nm =>
        match σ.(genv_tu).(symbols) !! nm with
        | None => False
        | Some ov =>
          let ty := type_of_value ov in
        if s.(s_virtual_dtor) then
          resolve_virtual (σ:=σ) (_eqv v) cls nm (fun da p =>
             |> fspec σ.(genv_tu).(globals) ty ti (Vptr da) (Vptr p :: nil) (fun _ => Q))
        else
           Exists da, _global nm &~ da **
                              |> fspec σ.(genv_tu).(globals) ty ti (Vptr da) (v :: nil) (fun _ => Q)
        end
      | DtorDefault =>
        wp_dtor (Tnamed cls) (_eqv v) Q
          (* what would i do here?
           * - i need to define the semantics of a default destructor
           * - the only complexity with this would be virtual inheritence.
           *)
      end
    | _ => False
    end.

  (* [destruct_val t this dtor Q] invokes the destructor ([dtor]) on [this]
     with the type of [this] is [t].

     note: it does *not* free the underlying memory.
   *)
  Fixpoint destruct_val (t : type) (this : val) (Q : mpred)
           {struct t}
  : mpred :=
    match t with
    | Tqualified _ t => destruct_val t this Q
    | Tnamed cls =>
      destruct_obj cls this Q
    | Tarray t sz =>
      fold_right (fun i Q =>
         Exists p, _offsetL (_sub t (Z.of_nat i)) (_eqv this) &~ p ** destruct_val t (Vptr p) Q) Q (List.rev (seq 0 (N.to_nat sz)))
    | _ => emp
    end.

  (* call the destructor (if available) and delete the memory *)
  Definition mdestroy (ty : type) (this : val) (Q : mpred)
  : mpred :=
    destruct_val ty this (_at (_eqv this) (anyR (erase_qualifiers ty) 1) ** Q).

End destroy.
