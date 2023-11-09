Require Import bedrock.prelude.base.
  Require Import bedrock.prelude.bytestring.

Require Import bedrock.lang.cpp.syntax.names.
Require Import bedrock.lang.cpp.syntax.types.
Require Import bedrock.lang.cpp.syntax.translation_unit.


Module checker.
Section checker.

  Record classification : Set :=
    { scoped : bool ; pointee : bool ; complete : bool ; basic : bool }.
  #[local] Instance classification_eq_dec : EqDecision classification.
  Proof. solve_decision. Defined.

  Definition state := avl.IM.t classification.
  Definition M (t : Type) : Type :=
    state -> option (state * t).

  Instance M_ret : MRet M := fun _ x s => Some (s, x).
  Instance M_bind : MBind M := fun _ _ k c s =>
                                 match c s with
                                 | None => None
                                 | Some (s, x) => k x s
                                 end.
  Definition guard (P : Prop) {_ : Decision P} : M unit :=
    fun s => if bool_decide P then Some (s, tt) else None.

  #[local] Notation "'let*' x , .. , z := t 'in' f" :=
    (mbind (fun x => .. (fun z => f) ..) t) (only parsing, at level 200, x closed binder, z closed binder).
  #[local] Notation "'let*' := t 'in' f" :=
    (mbind (fun '() => f) t) (only parsing, at level 200).

  Definition is_complete (nm : globname) : M bool :=
    fun s =>
      Some (s, match s !! nm with
               | Some c => c.(complete)
               | _ => false
               end).

  Definition is_scoped (nm : globname) : M bool :=
    fun s =>
      Some (s, match s !! nm with
               | Some c => c.(scoped)
               | _ => false
               end).

  Section check_list.
    Context {A B : Type} (check : A -> M B).
    Fixpoint check_list (ls : list A) : M (list B) :=
      match ls with
      | nil => mret []
      | l :: ls =>
          cons <$> check l <*> check_list ls
      end.
  End check_list.

  (* basic -> pointee
     basic -> complete
     pointee -> complete (only functions)
     pointee -> scoped
     complete -> scoped
   *)

  Definition extend (c : classification) : classification :=
    {| basic := c.(basic)
     ; pointee := c.(pointee) || c.(basic)
     ; complete := c.(complete) || c.(basic)
     ; scoped := c.(scoped) || c.(complete) || c.(pointee) || c.(basic) |}.

  Definition intersect (a b : classification) : classification :=
    let a := extend a in
    let b := extend b in
    extend {| pointee := a.(pointee) && b.(pointee)
     ; scoped := a.(scoped) && b.(scoped)
     ; complete := a.(complete) && b.(complete)
     ; basic := a.(basic) && b.(basic) |}.
  Definition union (a b : classification) : classification :=
    let a := extend a in
    let b := extend b in
    extend {| pointee  := a.(pointee)  || b.(pointee)
            ; scoped   := a.(scoped)   || b.(scoped)
            ; complete := a.(complete) || b.(complete)
            ; basic    := a.(basic)    || b.(basic) |}.


  Definition mk_basic : classification :=
    {| basic := true
     ; pointee := true
     ; complete := true
     ; scoped := true |}.

  Definition null := Build_classification false false false false.

  Fixpoint classify_type (t : type) : M classification :=
    match t with
    | Tfloat_ _
    | Tnum _ _
    | Tchar_ _
    | Tarch _ _
    | Tbool
    | Tvoid
    | Tnullptr => mret mk_basic
    | Tqualified q t =>
        classify_type t
    | Tptr t =>
        let* c := classify_type t in
        mret $ extend {| basic := c.(pointee)
              ; complete := false
              ; scoped := false
              ; pointee := false |}
    | Tref t
    | Trv_ref t =>
        let* c := classify_type t in
        mret $ extend {| complete := c.(pointee)
                       ; scoped := false
                       ; pointee := true
                       ; basic := false |}
    | Tarray t n =>
        if bool_decide (0 < n)%N then
          let* c := classify_type t in
          mret $ extend {| complete := c.(complete)
                         ; scoped := c.(scoped)
                         ; basic := false ; pointee := true |}
        else mret null
    | Tnamed nm
    | Tenum nm =>
        let* (com : bool) := is_complete nm in
        let* (scp : bool) := is_scoped nm in
        mret $ extend {| complete := com
                       ; scoped := scp
                       ; basic := false
                       ; pointee := scp |}
    | Tfunction ret args =>
        let* c_ret := classify_type ret in
        let* c_args := check_list classify_type args in
        mret $ fold_left intersect c_args c_ret
    | Tmember_pointer cls t =>
        let* (c_cls : bool) := is_scoped cls in
        if c_cls then
          let* c_t := classify_type t in
          mret $ extend {| complete := c_t.(basic) || c_t.(pointee)
                         ; scoped := c_t.(scoped) ; basic := false ; pointee:=false |}
        else mret null
    end.

  Lemma bind_run {A B} m (k : A -> M B) s :
    (m ≫= k) s = match m s with
                 | None => None
                 | Some (s', x) => k x s'
                 end.
  Proof. done. Qed.

  (*
  Definition check_ok (tu : _) (s : state) : Prop :=
    forall nm (b : bool),
        s !! nm = Some b ->
        exists gd, tu !! nm = Some gd /\
                if b then complete_decl tu gd
                else True.

  Lemma is_complete_ok {tu s n sb} :
    check_ok tu s ->
    is_complete n s = Some sb ->
    s = sb.1 /\ match sb.2 with
             | true => exists gd, tu !! n = Some gd /\ complete_decl tu gd
             | false => True
             end.
  Proof. Admitted.

  Lemma is_scoped_ok {tu s n sb} :
    check_ok tu s ->
    is_scoped n s = Some sb ->
    s = sb.1 /\ match sb.2 with
             | true => exists gd, tu !! n = Some gd
             | false => True
             end.
  Proof. Admitted.

  #[local] Opaque is_scoped is_complete.

  Lemma classify_type_ok tu : forall s,
    check_ok tu s ->
    forall t,
      match classify_type t s with
      | None => True
      | Some (s, cls) =>
          match cls with
          | null => True
          | scoped => wellscoped_type tu t
          | pointee => complete_pointee_type tu t
          | complete => complete_type tu t
          | basic => complete_basic_type tu t
          end
      end.
  Proof.
    #[local] Ltac simplify :=
      repeat (match goal with
              | |- context [ (_ ≫= _) _ ] =>
                  rewrite bind_run
              | H : _ |- _ => rewrite bind_run in H
              | H : match ?X with _ => _ end |- context [ ?X ] =>
                  destruct X eqn:?
              | |- _ => progress (try subst; simpl in *; auto)
              | H : exists x , _ |- _ => destruct H
              | H : _ /\ _ |- _ => destruct H
              | H : prod _ _ |- _ => destruct H
              | H : check_ok _ _ , H' : is_complete _ _ = _ |- _ =>
                  apply (is_complete_ok H) in H'
              | H : check_ok _ _ , H' : is_scoped _ _ = _ |- _ =>
                  apply (is_scoped_ok H) in H'
              | H : mret _ _ = Some _ |- _ => inversion H; clear H
              | |- context [ bool_decide _ ] => case_bool_decide
              | |- _ => (case_match; try solve [ congruence | auto ]); []
              end).
    induction t; simpl; simplify;
      try solve [ constructor | constructor; first [ assumption | lia ] ].
    { admit. }
    { case_match; subst; auto.
      case_match; auto; simplify.
      + eapply complete_named; eauto.
      + simplify.
        case_match; simplify.
        econstructor. eauto. }
    { case_match; simplify.
      + admit.
      + admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { destruct (is_scoped g s) eqn:?; auto; simplify.
      admit.
      admit.
      admit. }
    { admit. }
    { admit. }
  Admitted.
  *)

  Require Import bedrock.lang.cpp.syntax.types.
  Require Import bedrock.prelude.bytestring.

  Compute classify_type Tbool ∅.
  Eval vm_compute in classify_type (Tarray (Tnamed "x")%bs 10)
                       (<[ "x"%bs := null ]> ∅).

  Definition mk_complete := extend {| complete := true ; pointee := true ; scoped := true ; basic := false |}.

  Definition check_decl (gd : GlobDecl) : M classification :=
    match gd with
    | Gtype => mret {| scoped := true ; basic := false ; pointee := true ; complete := false |}
    | Gstruct s =>
        let* bs := check_list (fun x => classify_type (Tnamed x.1)) s.(s_bases) in
        let* fs := check_list (fun m => classify_type m.(mem_type)) s.(s_fields) in
        let x := fold_left intersect (bs ++ fs) mk_complete in
        mret $ if x.(complete) then mk_complete else null
    | Gunion u =>
        let* fs := check_list (fun m => classify_type m.(mem_type)) u.(u_fields) in
        let x := fold_left intersect fs mk_complete in
        mret $ if x.(complete) then mk_complete else null
    | Genum ty _ =>
        let* c := classify_type ty in
        mret $ extend {| complete := c.(basic)
                       ; scoped := false ; pointee := true ; basic := false |}
    | Gtypedef ty =>
        classify_type ty
    | Gconstant _ _ => mret null
    end.

  Definition classify (nm : globname) (c : classification) : M bool :=
    fun s =>
      match s !! nm with
      | None => Some (<[ nm := c ]> s, true)
      | Some c_old =>
          let cc := union c c_old in
          if bool_decide (cc = c_old)
          then Some (s, false)
          else Some (<[ nm := cc ]> s, true)
      end.

  Definition mk_scoped :=
    extend {| scoped := true ; pointee := false ; basic := false ; complete := false |}.

  Fixpoint check_all (ls : list (globname * GlobDecl)) (acc : bool) : M bool :=
    match ls with
    | nil => mret acc
    | (nm, gd) :: ls =>
        let* c_init := is_complete nm in
        if c_init is true
        then check_all ls acc
        else
          let* n :=
            match gd with
            | Gtypedef _ => mret false
            | _ => classify nm mk_scoped
            end in
          let* b := check_decl gd ≫= classify nm in
          check_all ls (n || b || acc)
    end.

  Fixpoint iterate (m : M bool) (n : nat) : M bool :=
    match n with
    | 0 => mret false
    | S n =>
        let* (x : bool) := m in
        if x then iterate m n else mret true
    end.

  Definition summarize_tu (tu : translation_unit) : _ :=
    let ls := avl.IM.elements tu.(types) in
    match iterate (check_all ls false) (S $ length ls) ∅ with
    | None => ∅
    | Some (s, _) => s
    end.

  Definition check_tu (tu : translation_unit) : list _ :=
    List.flat_map (fun a => match tu.(types) !! a.1 with
                         | Some (Gconstant _ _) => []
                         | Some Gtype => []
                         | Some ((Gstruct _ | Gunion _ | Genum _ _ | Gtypedef _) as gd) =>
                             if a.2.(checker.complete) then []
                             else [(a.1, Some (gd, a.2))]
                         | _ => [(a.1, None)]
                         end) $ avl.IM.elements (summarize_tu tu).

End checker.
End checker.

(*
Require bedrock.lang.cpp.test_cpp.

Eval vm_compute in checker.check_tu test_cpp.module.
*)


  (*

  Definition check_basic pointee (t : type) : M bool :=
    match t with
    | Tfloat_ _
    | Tnum _ _
    | Tbool
    | Tvoid
    | Tnullptr => mret true
    | Tptr t => pointee t
    | _ => mret false
    end.



  Fixpoint complete_basic_type (t : type) : M bool :=
    (* DONE *)
    check_basic complete_pointee_type t
  with complete_pointee_type (t : type) : M bool :=
    (* *)
    match t with
    | Tqualified _ t => complete_pointee_type t
    | Tarray t n =>
        let* := guard (n <> 0%N) in
        complete_pointee_type t
    | Tnamed nm =>
        match tu.(types) !! nm with
        | Some (Gstruct _ | Gunion _ | Gtype) => mret true
        | _ => mret false
        end
    | Tenum nm =>
        match tu.(types) !! nm with
        | Some (Genum ty _) => rec_complete_basic_type ty
        | _ => mret false
        end
    | Tfunction ret args =>
        andb <$> wellscoped_type ret <*> check_list wellscoped_type args
    | _ => check_basic complete_pointee_type t
    end
  with complete_type (t : type) : M bool :=
    let check_complete_decl nm :=
      match tu.(types) !! nm with
      | Some ((Gstruct _ | Gunion _) as gd) => rec_complete_decl gd
      | _ => mret false
      end
    in
    match t with
    | Tqualified _ t => complete_type t
    | Tref t => complete_type t
    | Trv_ref t => complete_type t
    | Tnamed nm => check_complete_decl nm
    | Tarray t n =>
        let* := guard (n <> 0%N) in
        complete_type t
    | Tmember_pointer n t =>
        let* := guard (not_ref_type t) in
        let* := guard False in
        complete_pointee_type t
    | Tfunction ret args =>
        andb <$> wellscoped_type ret <*> check_list wellscoped_type args
    | _ => check_basic complete_pointee_type t
    end

  with wellscoped_type (t : type) : M bool :=
     let check_complete_decl nm :=
      match tu.(types) !! nm with
      | Some ((Gstruct _ | Gunion _) as gd) => rec_complete_decl gd
      | _ => mret false
      end
    in
    match t with
    | Tqualified _ t => wellscoped_type t
    | Tarray t n =>
        let* := guard (0 < n)%N in
        wellscoped_type t
      (* pointee type *)
    | Tnamed nm =>
        match tu.(types) !! nm with
        | Some (Gstruct _ | Gunion _ | Gtype) => mret true
        | _ => mret false
        end
    | Tenum nm =>
        match tu.(types) !! nm with
        | Some (Genum ty _) => rec_complete_basic_type ty
        | _ => mret false
        end
    | Tfunction ret args =>
        andb <$> wellscoped_type ret <*> check_list wellscoped_type args
      (* complete *)
    | Tref t => complete_type t
    | Trv_ref t => complete_type t
    | Tmember_pointer n t =>
        let* := guard (not_ref_type t) in
        let* := guard False in
        complete_pointee_type t
    | _ => check_basic complete_pointee_type t
    end.
  End fixpoint.

  Fixpoint


  (* with well-founded translation units + a strong type system, we can reduce some
     our complexity. *)
  (*
  Fixpoint check_complete (t : type) : M bool :=
    match t with
    | Tfloat_ _
    | Tnum _ _
    | Tbool
    | Tvoid
    | Tnullptr => mret complete
    | Tqualified q t =>
        classify_type t
    | Tptr t
    | Tref t
    | Trv_ref t =>
        let* c := classify_type t in
        mret match c with
             | basic | pointee | complete => complete
             | scoped => scoped
             | null => null
             end
    | Tarray t n =>
        let* c := classify_type t in
        mret match c with
             | complete => complete
             | scoped => scoped
             | _ => null
             end
    | Tnamed nm =>
    | _ => mret null
    end.
  *)

  (* XXX *)


  (*
  Variable rec_complete_decl : GlobDecl -> M bool.
  Variable rec_complete_basic_type : type -> M bool.
  Variable rec_complete_pointee_type : type -> M bool.
  Variable rec_complete_type : type -> M bool.
  Variable rec_wellscoped_type : type -> M bool.
  *)

  (*
  Print well_founded.



  Inductive type_acc : type -> type -> Prop :=
  | acc_ptr {t} : type_acc t (Tptr t)
  | acc_ref {t} : type_acc t (Tref t)
  | acc_rv_ref {t} : type_acc t (Trv_ref t)
  | acc_array {t n} : type_acc t (Tarray t n)
  | acc_named_struct_field {t nm s} :
    tu.(types) !! nm = Some (Gstruct s) ->
    In t (mem_type <$> s.(s_fields)) ->
    type_acc t (Tnamed nm)
  | acc_named_struct_base {nm base s} :
    tu.(types) !! nm = Some (Gstruct s) ->
    In base (fst <$> s.(s_bases)) ->
    type_acc (Tnamed base) (Tnamed nm)
  | acc_named_union_field {t nm u} :
    tu.(types) !! nm = Some (Gunion u) ->
    In t (mem_type <$> u.(u_fields)) ->
    type_acc t (Tnamed nm).



  (* Definition complete_decl (d : GlobDecl) : bool :=
    match d with
    | Gstruct s => false
    | Gunion u => false
    | _ => false
    end
  with wellscoped_types (ts : list type) : bool :=
    match ts with
    | nil => true
    | t :: ts => wellscoped_type t && wellscoped_types ts
    end.
   *)
*)
*)
