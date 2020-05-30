(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier:AGPL-3.0-or-later
 *)
Require Import Coq.Lists.List.

Require Import stdpp.telescopes.

From iris.proofmode Require Import tactics.
From bedrock Require Import ChargeUtil ChargeCompat.

From bedrock.lang.cpp Require Import ast semantics spec.
From bedrock.lang.cpp Require Import
     pred path_pred heap_pred
     wp intensional.

Local Set Universe Polymorphism.

Section with_cpp.
  Context `{Σ : cpp_logic thread_info} {resolve:genv}.

  (* Hoare triple for a function.
   * note(gmm): these should include linkage specifications.
   *)
  Definition TSFunction@{X Z Y} (ret : type) (targs : list type)
             (PQ : thread_info -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    {| fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec ti   := WppD (PQ ti) |}.


  Definition SFunction@{X Z Y} (ret : type) (targs : list type)
             (PQ : WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    {| fs_return    := ret
     ; fs_arguments := targs
     ; fs_spec _    := WppD PQ |}.

  Local Notation anyR := (@anyR _ Σ resolve) (only parsing).
  Local Notation primR := (@primR _ Σ resolve) (only parsing).

  (* Hoare triple for a constructor.
   *)
  Definition SConstructor@{X Z Y} (class : globname)
             (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let map_pre this '(args, P) :=
        (this :: args,
         _at (_eqv this) (anyR (Tnamed class) 1) ** P) in
    let this_type := Qmut (Tnamed class) in
    SFunction (Qmut Tvoid) (Qconst (Tpointer this_type) :: targs)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre (Vptr this)) (PQ this).(wpp_pre)
               ; wpp_post this := (PQ this).(wpp_post)
               |}.

  (* Hoare triple for a destructor.
   *)
  Definition SDestructor@{X Z Y} (class : globname)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let map_pre this '(args, P) := (Vptr this :: args, P) in
    let map_post this '{| we_ex := pwiths ; we_post := Q|} :=
        {| we_ex := pwiths
         ; we_post := tele_map (fun '(result, Q) =>
                                  (result, _at (_eq this) (anyR (Tnamed class) 1) ** Q)) Q |}
    in
    let this_type := Qmut (Tnamed class) in
    SFunction@{X Z Y} (Qmut Tvoid) (Qconst (Tpointer this_type) :: nil)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre this) (PQ this).(wpp_pre)
               ; wpp_post this :=
                   tele_map (map_post this) (PQ this).(wpp_post)
              |}.

  (* Hoare triple for a method.
   *)
  Definition SMethod@{X Z Y} (class : globname) (qual : type_qualifiers)
             (ret : type) (targs : list type)
             (PQ : ptr -> WithPrePost@{X Z Y} mpredI)
  : function_spec :=
    let map_pre this '(args, P) := (this :: args, P) in
    let class_type := Tnamed class in
    let this_type := Tqualified qual class_type in
    SFunction ret (Qconst (Tpointer this_type) :: targs)
              {| wpp_with := TeleS (fun this : ptr => (PQ this).(wpp_with))
               ; wpp_pre this :=
                   tele_map (map_pre (Vptr this)) (PQ this).(wpp_pre)
               ; wpp_post this := (PQ this).(wpp_post)
               |}.

  Definition bind_base_this (o : option ptr) (rty : type) (Q : region -> mpred) : mpred :=
    if is_aggregate rty then
      Forall ra : ptr, _at (_eq ra) (anyR (erase_qualifiers rty) 1) -*
                       Q (Remp o (Some ra))
    else Q (Remp o None).

  Definition Rbind_check (x : ident) (p : ptr) (r : region) : region :=
    if decide (x = ""%bs)
    then r
    else Rbind x p r.

  Fixpoint bind_vars (args : list (ident * type)) (vals : list val) (r : region) (Q : region -> FreeTemps -> mpred) : mpred :=
    match args , vals with
    | nil , nil => Q r empSP
    | (x,ty) :: xs , v :: vs  =>
      match drop_qualifiers ty with
      | Tqualified _ t => ltrue (* unreachable *)
      | Treference    _
      | Trv_reference _
      | Tnamed _ =>
        match v with
        | Vptr p => bind_vars xs vs (Rbind_check x p r) Q
        | _ => lfalse
        end
      | _              =>
        Forall a, _at (_eq a) (primR (erase_qualifiers ty) 1 v) -*
        bind_vars xs vs (Rbind_check x a r) (fun r free => Q r (_at (_eq a) (anyR (erase_qualifiers ty) 1) ** free))
      end
    | _ , _ => lfalse
    end.

  (* the meaning of a function
   *)
  Definition wp_func (f : Func) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match f.(f_body) with
    | None => lfalse
    | Some body =>
      bind_base_this None f.(f_return) (fun ρ =>
      bind_vars f.(f_params) args ρ (fun ρ frees =>
      if is_void f.(f_return) then
        wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid)))
      else
        wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |> Q x)))))
    end.

  Definition func_ok (f : Func) (ti : thread_info) (spec : function_spec)
    : mpred :=
      [| type_of_spec spec =
         normalize_type (Tfunction f.(f_return) (List.map snd f.(f_params))) |] **
      (* forall each argument, apply to [fs_spec ti] *)
      □ Forall Q : val -> mpred, Forall vals,
        spec.(fs_spec) ti vals Q -* wp_func f ti vals Q.

  Definition wp_method (m : Method) ti (args : list val)
             (Q : val -> epred) : mpred :=
    match m.(m_body) with
    | None => lfalse
    | Some body =>
      match args with
      | Vptr thisp :: rest_vals =>
        bind_base_this (Some thisp) m.(m_return) (fun ρ =>
        bind_vars m.(m_params) rest_vals ρ (fun ρ frees =>
        if is_void m.(m_return) then
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|>Q Vvoid)))
        else
          wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (val_return (fun x => |>Q x)))))
      | _ => lfalse
      end
    end.

  Definition method_ok (m : Method) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec =
       normalize_type (Tfunction m.(m_return) (Tpointer (Tqualified m.(m_this_qual) (Tnamed m.(m_class))) :: List.map snd m.(m_params))) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_method m ti vals Q.

  Require Import bedrock.lang.cpp.heap_notations.

  Definition _instance_of (mdc cls : globname) (q : Qp) : Rep :=
    as_Rep (fun this => @instance_of _ _ resolve mdc cls q this).

  Fixpoint all_identities (f : nat) (mdc : globname) (cls : globname) : Rep.
  refine
    match f with
    | 0 => lfalse
    | S f =>
      match resolve.(genv_tu).(globals) !! cls with
      | Some (Gstruct st) =>
        _instance_of mdc cls 1 **
        [∗list] b ∈ st.(s_bases),
           let '(base,_) := b in
           _base resolve cls base |-> all_identities f mdc base
      | _ => lfalse
      end
    end.
  Defined.


  Definition init_identity (thisp : ptr) (cls : globname) (Q : mpred) : mpred :=
    match resolve.(genv_tu).(globals) !! cls with
    | Some (Gstruct st) =>
      ([∗list] b ∈ st.(s_bases),
         let '(base,_) := b in
         thisp ., _base resolve cls base |-> all_identities 100 base base) **
      (_eq thisp |-> _instance_of cls cls 1 -*
       ([∗list] b ∈ st.(s_bases),
          let '(base,_) := b in
          thisp ., _base resolve cls base |-> all_identities 100 cls base) -* Q)
    | _ => lfalse
    end.

  Fixpoint wpi_members
           (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (inits : list Initializer)
           (Q : mpred -> mpred) : mpred :=
    match inits with
    | nil => Q empSP
    | i :: is' =>
      match i.(init_path) with
      | This
      | Base _ => lfalse
      | _ => wpi (resolve:=resolve) ⊤ ti ρ cls (Vptr this) i (fun f => f ** wpi_members ti ρ cls this is' Q)
      end
    end.

  Fixpoint wpi_bases (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (inits : list Initializer)
           (Q : mpred -> mpred) : mpred :=
    match inits with
    | nil => init_identity this cls (Q empSP)
    | i :: is' =>
      match i.(init_path) with
      | Field _
      | Indirect _ _ =>
        init_identity this cls (wpi_members ti ρ cls this inits Q)
      | _ => wpi (resolve:=resolve) ⊤ ti ρ cls (Vptr this) i (fun f => f ** wpi_members ti ρ cls this is' Q)
      end
    end.

  Parameter _classR : genv -> globname -> Qp -> bool -> Rep.
  (* this represents a pointer to the vtable for the given class.
   * if the class does not have any virtual functions, then this is [emp]
   * the boolean represents whether it is initialized.
   * - we don't really need to worry about whether the compiler 
   *
   * this essentially factors into:
   * - _vptr : genv -> globname -> Offset
   *   (the location of the _vptr (even the existance of one) depends on the class)
   * - _vtable : globname -> option (gmap obj_name ptr) -> Qp -> Rep
   *)

  (* note(gmm): supporting virtual inheritence will require us to add
   * constructor kinds here
   *)
  Definition wp_ctor (ctor : Ctor)
             (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match ctor.(c_body) with
    | None => lfalse
    | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
    | Some (UserDefined (inits, body)) =>
      match args with
      | Vptr thisp :: rest_vals =>
        bind_base_this (Some thisp) Tvoid (fun ρ =>
        bind_vars ctor.(c_params) rest_vals ρ (fun ρ frees =>
          (wpi_bases ti ρ ctor.(c_class) thisp inits
             (fun free => free **
                        wp (resolve:=resolve) ⊤ ti ρ body (Kfree frees (void_return (|> Q Vvoid)))))))
      | _ => lfalse
      end
    end.

  Definition ctor_ok (ctor : Ctor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec =
       normalize_type (Tfunction Tvoid (Tpointer (Tnamed ctor.(c_class)) :: List.map snd ctor.(c_params))) |] **
    (* forall each argument, apply to [fs_spec ti] *)
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_ctor ctor ti vals Q.

  Definition revert_identity (thisp : ptr) (cls : globname) (Q : mpred) : mpred :=
    match resolve.(genv_tu).(globals) !! cls with
    | Some (Gstruct st) =>
      _eq thisp |-> _instance_of cls cls 1 **
      ([∗list] b ∈ st.(s_bases),
          let '(base,_) := b in
          thisp ., _base resolve cls base |-> all_identities 100 cls base) **
      (([∗list] b ∈ st.(s_bases),
         let '(base,_) := b in
         thisp ., _base resolve cls base |-> all_identities 100 base base) -* Q)
    | _ => lfalse
    end.


  Fixpoint wpd_bases (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (dests : list (FieldOrBase * globname))
           (Q : mpred) : mpred :=
    match dests with
    | nil => Q
    | d :: is' =>
      match d.1 with
      | Field _
      | Indirect _ _ => lfalse
      | _ => wpd (resolve:=resolve) ⊤ ti ρ cls (Vptr this) d
                (wpd_bases ti ρ cls this is' Q)
      end
    end.

  Fixpoint wpd_members
           (ti : thread_info) (ρ : region) (cls : globname) (this : ptr)
           (dests : list (FieldOrBase * globname))
           (Q : mpred) : mpred :=
    match dests with
    | nil => revert_identity this cls Q
    | d :: is' =>
      match d.1 with
      | This
      | Base _ =>
        revert_identity this cls (wpd_bases ti ρ cls this dests Q)
      | _ => wpd (resolve:=resolve) ⊤ ti ρ cls (Vptr this) d (wpd_members ti ρ cls this is' Q)
      end
    end.

  Definition wp_dtor (dtor : Dtor) (ti : thread_info) (args : list val)
             (Q : val -> epred) : mpred :=
    match dtor.(d_body) with
    | None => lfalse
    | Some Defaulted => lfalse
      (* ^ defaulted constructors are not supported yet *)
    | Some (UserDefined (body, deinit)) =>
      match args with
      | Vptr thisp :: rest_vals =>
        bind_base_this (Some thisp) Tvoid (fun ρ =>
        wp (resolve:=resolve) ⊤ ti ρ body
           (void_return (wpd_members ti ρ dtor.(d_class) thisp deinit (|> Q Vvoid))))
      | _ => lfalse
      end
    end.

  Definition dtor_ok (dtor : Dtor) (ti : thread_info) (spec : function_spec)
    : mpred :=
    [| type_of_spec spec =
       normalize_type (Tfunction Tvoid (Tpointer (Tnamed dtor.(d_class)) :: nil)) |] **
    □ Forall Q : val -> mpred, Forall vals,
      spec.(fs_spec) ti vals Q -* wp_dtor dtor ti vals Q.

End with_cpp.
