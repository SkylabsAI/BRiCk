(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 *
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
From bedrock.lang.bi Require Export monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import iris.bi.lib.fractional.


Require Import bedrock.prelude.base.

From bedrock.lang.cpp Require Import
  semantics ast logic.pred logic.path_pred logic.rep logic.rep_defs heap_notations
  heap_pred.


Section defs.
  Context `{Σ : cpp_logic}  {σ : genv}.
  
  Fixpoint const_coreR_aux (fuel : nat) (ty : type) (q : Qp) : Rep :=
    match fuel with
    | 0 => as_Rep $ const_core ty q
    | S n => 
        match ty with
        | Tptr _
        | Tref _
        | Trv_ref _ 
        | Tnum _ _
        | Tbool
        | Tnullptr
        | Tvoid => anyR ty (q / 2)

        | Tarray _ _ => False (* TODO *)
        | Tnamed cls => match glob_def σ cls with
                       | None => False
                       | Some gd =>
                           match gd with 
                           | Gtype => False
                           | Gunion _ => False
                           | Gstruct str => False
                           | Genum _ _ => False
                           | Gconstant _ _ => False 
                           | Gtypedef _ => False
                           end
                       end
        | Tqualified t_c ty' =>
            match t_c with
            | QCV | QC =>  const_coreR_aux n ty' (q/2)
            (* ^ assumes that there are not multiple [Tqualified] in a row *)
            | _ => const_coreR_aux n ty' q
            end
        | Tenum _ => False (* TODO *) 

        | Tmember_pointer _ _
        | Tfloat _
        | Tfunction _ _
        | Tarch _ _ => False 
        end
    end.

  Definition const_coreR : type -> Qp -> Rep := const_coreR_aux 3.


  Lemma const_coreR_primrR_Tptr ty ty' q v :
    ty = Tptr ty' ->
    primR ty (q + q / 2) v -|- const_coreR ty q ** primR ty q v.
  Proof.
    case: ty=>>//= [->].
    
    rewrite (@fractional _ _ (primR_fractional _ _ _)).
    rewrite /const_coreR.

    iSplit.
    + iIntros "[??]". iFrame.
      by iApply primR_anyR. 
    + iIntros "[??]". iFrame.
      admit.

  Admitted.
  
  Lemma const_coreR_Tconst ty q :
    (forall t_c' ty', ty <> Tqualified t_c' ty') ->
    const_coreR (Tqualified QC ty) q -|- const_coreR ty (q / 2).
  Proof.
    rewrite /const_coreR/=.
    case: ty; auto.
    move=>t_c ty /(_ t_c ty) //=.
  Qed.
  
    
  
  




  
