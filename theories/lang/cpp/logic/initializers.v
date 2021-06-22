(*
 * Copyright (c) 2020 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import Coq.Lists.List.
Require Import iris.proofmode.tactics.
Require Import bedrock.lang.prelude.numbers.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.bi.errors.
From bedrock.lang.cpp.logic Require Import
     pred path_pred heap_pred wp destroy.
Require Import bedrock.lang.cpp.heap_notations.

Module Type Init.

  Section with_resolve.
    Context `{Σ : cpp_logic thread_info} {σ:genv}.
    Variables (M : coPset) (ti : thread_info) (ρ : region).

    #[local] Notation wp := (wp (resolve:=σ) M ti ρ).
    #[local] Notation wp_lval := (wp_lval (resolve:=σ) M ti ρ).
    #[local] Notation wp_prval := (wp_prval (resolve:=σ) M ti ρ).
    #[local] Notation wp_xval := (wp_xval (resolve:=σ) M ti ρ).
    #[local] Notation wp_operand := (wp_operand (resolve:=σ) M ti ρ).
    #[local] Notation wp_init := (wp_init (resolve:=σ) M ti ρ).
    #[local] Notation fspec := (@fspec _ Σ σ.(genv_tu).(globals)).
    #[local] Notation mspec := (@mspec _ Σ σ.(genv_tu).(globals)).

    (** * Array initialization *)
    Section init_array.
      Variable (ty : type).

      Section with_base.
        Variable (base : ptr).

        Fixpoint initialize_array' (inits : list (ptr -> (FreeTemp -> FreeTemps -> mpred) -> mpred))
                 (idx : Z) (Q : FreeTemp -> FreeTemps -> mpred)
                 {struct inits} : mpred :=
          match inits return mpred with
          | nil => emp (* base .[ ty ! idx ] |-> validR -* Q (fun x => x) (fun x => x) *)
          | init :: inits =>
            init (base .[ ty ! idx ]) (fun free' frees' =>
              initialize_array' inits (1 + idx)%Z (fun free frees => Q (free >*> free') (frees >*> frees')))%free
          end.
      End with_base.

      (** [init_array ty inits Q] constructs an array of [ty] using [inits].
          The signature follows the signature of [wp_prval], so
          [Q base free frees] means that [base] is the base of the array,
          [free] is the destructor for the array, and [frees] is the destructor
          for temporaries that were created during the creation of the array.

          [inits] is expressed as a list of [wp_prval]-like functions in order
          to share the logic between array initialization and default
          initialization (which doesn't have any expressions).
       *)
      Definition init_array (inits : list (ptr -> (FreeTemp -> FreeTemps -> mpred) -> mpred))
                 (Q : ptr -> FreeTemp -> FreeTemps -> mpred) : mpred :=
        Forall base, initialize_array' base inits 0 (Q base).

    End init_array.



    Section default_initialize.
      Variable (default_initialize : type -> ptr -> (FreeTemps -> mpred) -> mpred).
      Variable (ty : type).

      Definition default_initialize_array (len : N) (p : ptr) (Q : FreeTemp -> mpred) : mpred :=
          (fix rec (ls : list N) frees :=
             match ls with
             | nil => p .[ ty ! Z.of_N len ] |-> validR -* Q frees
             | l :: ls =>
               default_initialize ty (p .[ ty ! Z.of_N l ]) (rec ls)
             end)
          (seqN 0 len) FreeTemps.id.

      Lemma default_initialize_array_frame : ∀ sz Q Q' (p : ptr),
          (Forall f, Q f -* Q' f)
            |-- <pers> (Forall p Q Q', (Forall f, Q f -* Q' f) -* default_initialize ty p Q -* default_initialize ty p Q')
                         -* default_initialize_array sz p Q -* default_initialize_array sz p Q'.
      Proof.
        intros sz Q Q' p; rewrite /default_initialize_array.
        generalize dependent (p .[ ty ! Z.of_N sz ] |-> validR).
        induction (seqN 0 sz) =>/=; intros.
        - iIntros "X #Y a b"; iApply "X"; iApply "a"; eauto.
        - iIntros "F #Hty". iApply "Hty". iIntros (?). (* iApply IHl. ; eauto. *)
      Admitted.
    End default_initialize.

    (** [default_initialize ty p Q] default initializes the memory at [p] according to
        the type [ty].

        NOTE this assumes that the underlying memory has already been given to the
             C++ abstract machine.
     *)
    Fixpoint default_initialize
               (ty : type) (Q : ptr -> FreeTemp -> FreeTemps → epred) {struct ty} : mpred :=
      match ty with
      | Tint _ _ as rty
      | Tptr _ as rty
      | Tbool as rty
      | Tfloat _ as rty =>
        let rty := erase_qualifiers rty in
        Forall p : ptr, p |-> uninitR rty 1 -* Q p (delete_val ti rty p) (fun x => x)
      | Tarray ty sz =>
        False (* default_initialize_array default_initialize ty sz p Q *)
      | Tnullptr => UNSUPPORTED "default initialization of [nullptr_t]"

      | Tref _
      | Trv_ref _ => ERROR "default initialization of reference"
      | Tvoid => ERROR "default initialization of void"
      | Tfunction _ _ => ERROR "default initialization of functions"
      | Tmember_pointer _ _ => ERROR "default initialization of member pointers"
      | Tnamed _ => False (* default initialization of aggregates is done at elaboration time. *)

      | Tarch _ _ => UNSUPPORTED "default initialization of architecture type"
      | Tqualified _ ty => default_initialize ty Q
      end.

    Lemma default_initialize_frame:
      ∀ ty Q Q',
        Forall p f fs, Q p f fs -* Q' p f fs
        |-- default_initialize ty Q -* default_initialize ty Q'.
    Proof.
      induction ty; simpl;
        try solve [ intros; iIntros "a b c"; iApply "a"; iApply "b"; eauto | eauto ].
(*
      iIntros (? ? ?) "X"; iApply (default_initialize_array_frame with "X").
      iModIntro. iIntros (???). iApply IHty.
*)
    Admitted.

    (* [wp_initialize ar ty addr init Q] uses the expression [init] to initialize
       an object of type [ty] at location [addr]. Setting [ar:=true] means that
       references will be allocated as [primR ... 1 p] which is used when initializing
       an object.

       NOTE The memory at [addr] has already been given to the C++ abstract machine.

       NOTE it should be reasonable to remove [addr] entirely? or provide an
       [wp_initialize_at] that initializes at a location (only this version would
       need [alloc_ref:=true].

       TODO a more uniform semantics would *always* allocate a reference cell.
     *)
    Definition wp_initialize (alloc_ref : bool) (ty : type) (addr : ptr) (init : Expr) (k : FreeTemp -> FreeTemps -> mpred) : mpred :=
      match drop_qualifiers ty with
      | Tvoid => False
      | Tpointer _ as ty
      | Tmember_pointer _ _ as ty
      | Tbool as ty
      | Tnullptr as ty
      | Tint _ _ as ty =>
        wp_init addr init k
        (* non-primitives are handled via prvalue-initialization semantics *)

      | Tarray _ _
      | Tnamed _ => wp_init addr init k
        (* NOTE because we are initializing an object, we drop the destruction of the temporary *)

      | Treference _ =>
        if alloc_ref then
          wp_lval init (fun p free =>
                          addr |-> primR (erase_qualifiers ty) 1 (Vptr p) -*
                          k (fun x => addr |-> primR ty 1 (Vptr p) ** x) free)
        else
          wp_lval init (fun p free => [| p = addr |] -* k (fun x => x) free)

      | Trv_reference _ as ty =>
        if alloc_ref then
          wp_lval init (fun p free =>
                          addr |-> primR ty 1 (Vptr p) -*
                          k (fun x => addr |-> primR ty 1 (Vptr p) ** x) free)
        else
          wp_lval init (fun p free => [| p = addr |] -* k (fun x => x) free)

      | Tfunction _ _ => False (* functions not supported *)

      | Tqualified _ ty => False (* unreachable *)
      | Tarch _ _ => False (* vendor-specific types are not supported *)
      | Tfloat _ => False (* floating point numbers are not supported *)
      end.

    Lemma wp_initialize_frame ar obj ty e Q Q' :
      (Forall free frees, Q free frees -* Q' free frees) |-- wp_initialize ar ty obj e Q -* wp_initialize ar ty obj e Q'.
    Proof using.
      rewrite /wp_initialize.
      case_eq (drop_qualifiers ty) =>/=; intros; eauto;
        try solve [ iIntros "a"; iApply wp_prval_frame; try reflexivity;
                    iIntros (v ? fs) "X %"; iApply "a"; iApply "X"; eauto ].
      { iIntros "a".
        destruct ar; iApply wp_lval_frame; try reflexivity;
          [ iIntros (v f) "X Y" | iIntros (v f) "X %"]; iApply "a"; iApply "X"; eauto. }
      { iIntros "a".
        destruct ar; iApply wp_lval_frame; try reflexivity;
          [ iIntros (v f) "X Y" | iIntros (v f) "X %"]; iApply "a"; iApply "X"; eauto. }
    Qed.

    Lemma wp_initialize_wand ar obj ty e Q Q' :
      wp_initialize ar ty obj e Q |--(Forall free frees, Q free frees -* Q' free frees) -* wp_initialize ar ty obj e Q'.
    Proof using.
      iIntros "A B"; iRevert "A"; iApply wp_initialize_frame; eauto.
    Qed.

    Definition wpi (cls : globname) (thisp : ptr) (init : Initializer) (Q : _) : mpred :=
        let p' := thisp ., offset_for cls init.(init_path) in
        wp_initialize true (erase_qualifiers init.(init_type)) p' init.(init_init) (fun _ => Q).

  End with_resolve.

  Theorem wpi_frame (thread_info : biIndex) (Σ : cpp_logic thread_info) (σ1 σ2 : genv) (M : coPset) (ti : thread_info) (ρ : region)
          (cls : globname) (this : ptr) (e : Initializer) (k1 k2 : FreeTemps → mpredI) :
    genv_leq σ1 σ2 → Forall f1 f2, FreeTemps.wand f1 f2 -* k1 f1 -* k2 f2 |-- wpi M ti ρ cls this e k1 -* wpi M ti ρ cls this e k2.
  Proof.
    intros. assert (σ1 = σ2) by admit. subst.
    rewrite /wpi.
    iIntros "X"; iApply wp_initialize_frame.
    iIntros (??). iApply "X".
    (** TODO this is blocked on Properness of continuations, maybe [FreeTemp] should build this in? *)
  Admitted.

End Init.

Declare Module IN : Init.

Export IN.
