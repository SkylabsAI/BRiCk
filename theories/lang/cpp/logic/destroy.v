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

  Instance fold_left_ne {T : ofeT} {U : Type} {n} :
    Proper ((dist n ==> pointwise_relation _ (dist n)) ==> eq ==> dist n ==> dist n) (@fold_left T U).
  Proof.
    do 4 red; intros f1 f2 Hf xs1 _ <-.
    induction xs1; simpl; first done.
    intros x1 x2 Hx.
    eapply IHxs1, Hf, Hx.
  Qed.

  Unset Program Cases.

  Program Definition wp_dtor_pre (wp_dtor : type -d> Loc -d> mpredI -n> mpredI)
    : type -d> Loc -d> mpredI -n> mpredI :=
    λ t this, λne Q,
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
                              |> wp_dtor (Tnamed base) (_offsetL (_base σ cls base) this) Q) st.(s_bases) Q
             in
             fold_left (fun Q '(x,ty,_,_) =>
                          match drop_qualifiers ty with
                          | Tnamed nm =>
                            let l' := _offsetL (_field (resolve:=σ) {| f_type := cls ; f_name := x |}) this  in
                            |> wp_dtor ty l' Q
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
         | Some (Genum t _) => |> wp_dtor t this Q
         | _ => False
         end
       | _ => Q
       end%I.
  Next Obligation.
  (* Instance wp_dtor_pre_ne : ∀ (wp_dtor : type -d> Loc -d> mpredI -n> mpredI) (t : type)
    (this : Loc) (n : nat),
    Proper (dist n ==> dist n) (λ Q : mpredI, wp_dtor_pre wp_dtor t this Q).
  Proof. *)
    intros wp_dtor t this n Q1 Q2 HQ.
    (* unfold wp_dtor_pre. *)
    simpl.
    repeat case_match; try fast_done; first last. {
      f_contractive.
      by apply ofe_mor_car_ne, dist_S, HQ.
    }
    by repeat f_equiv.
    apply fold_left_ne, fold_left_ne; try done;
      intros Q1' Q2' HQ' a;
      repeat case_match => //; f_contractive;
      by apply ofe_mor_car_ne, dist_S, HQ'.
  Qed.

  Instance wp_dtor_pre_contractive : Contractive wp_dtor_pre.
  Proof.
    intros n f1 f2 Hf t this Q.
    unfold wp_dtor_pre; simpl.
    repeat case_match; try fast_done; first last. {
      f_contractive.
      apply Hf.
    }
    repeat f_equiv; intros Q1 Q2 HQ a;
      repeat case_match => //; f_contractive;
      apply dist_S in HQ; rewrite HQ;
      apply Hf.
  Qed.

  Definition wp_dtor : type -d> Loc -d> mpredI -n> mpredI :=
    fixpoint wp_dtor_pre.

  Lemma wp_dtor_unfold : wp_dtor ≡ wp_dtor_pre wp_dtor.
  Proof. apply fixpoint_unfold. Qed.

  Lemma wp_dtor_unfold_eta t this Q : wp_dtor t this Q ≡ wp_dtor_pre wp_dtor t this Q.
  Proof. apply wp_dtor_unfold. Qed.

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

End destroy.
