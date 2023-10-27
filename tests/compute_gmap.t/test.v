Require Import bedrock.prelude.gmap.
Require Import bedrock.lang.cpp.parser.

#[local] Open Scope bs_scope.

Ltac compute_translation_unit t :=
  let t := eval hnf in t in
  let symbols := compute_gmap.compute_gmap (t.(symbols)) in
  let types := compute_gmap.compute_gmap (t.(types)) in
  let initializer := eval vm_compute in (t.(initializer)) in
  let byte_order := eval vm_compute in (t.(byte_order)) in
  exact {| symbols := symbols; types := types; initializer := initializer; byte_order := byte_order |}.

(* 1.7 seconds for 1000 functions, versus 0.8 on master pre-8.18-bump. *)
(* 38 seconds for 5000 functions, versus 3.5 on master pre-8.18-bump. *)
(* Way too long for 10000 functions, versus stack overflow on master pre-8.18-bump. *)

Definition module_10 : translation_unit := ltac:(compute_translation_unit constr:(
  decls (
    (Dfunction "_Z2f1i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f2i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f3i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f4i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f5i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f6i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f7i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f8i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z2f9i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    (Dfunction "_Z3f10i"
      (Build_Func Tint
        (("x", Tint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Sreturn_val
                  (Ecast Cl2r (Evar (Lname "x") Tint) Prvalue Tint)) :: nil)))))) ::
    nil
  ) Little)).
