Require Import stdpp.fin_maps.
Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
From bedrock.lang.cpp.logic Require Import pred heap_pred path_pred.

Section dispatch.
  Context `{Σ : cpp_logic} (σ : genv).

  Definition list_get {T} (t : obj_name) (l : list (obj_name * T)) : option T :=
    match List.find (fun '(t',_) => if decide (t = t') then true else false) l with
    | None => None
    | Some (_, k) => Some k
    end.

  (* the [Offset] to cast a [from] to a [to] *)
  Fixpoint base_to_derived `(d : class_derives σ to from) : Offset :=
    match d with
    | Derives_here st _ => _id
    | Derives_base base st _ _ _ _ d =>
      _dot (base_to_derived d) (_derived σ base to)
    end.

  (* the [Offset] to cast a [from] to a [to] *)
  Fixpoint derived_to_base `(d : class_derives σ from to) : Offset :=
    match d with
    | Derives_here st _ => _id
    | Derives_base base st _ _ _ _ d =>
      _dot (_base σ to base) (base_to_derived d)
    end.


  Fixpoint dispatch `(d : class_derives σ mdc from) (final : obj_name)
    : (option obj_name * Offset (* from -> cls with obj_name *)) *
      obj_name :=
    match d with
    | Derives_here st _ =>
      ((mjoin (list_get final st.(s_virtuals)), _id), final)
    | Derives_base base st _ _ _ _ d' =>
      let '(result, cand) := dispatch d' final in
      match list_get cand st.(s_overrides) with
      | None => (result, cand)
      | Some cand =>
        ((mjoin (list_get cand st.(s_virtuals)), base_to_derived d),
         cand)
      end
    end.

  Definition get_impl `(r : class_derives σ mdc tcls) (f : obj_name)
    : option (ptr * Offset) :=
    let '(sym, off) := (dispatch r f).1 in
    match sym with
    | None => None
    | Some s => match glob_addr σ s with
               | None => None
               | Some p => Some (p, off)
               end
    end.

End dispatch.
Arguments get_impl {_ _ σ} {_ _} _ f : rename.

(* [resolve_virtual σ this cls f Q] returns [Q fa this'] if resolving [f] on
 * [this] results in a function that is equivalent to calling the pointer [fa]
 * passing [this'] as the "this" argument.
 *)
Definition resolve_virtual `{Σ : cpp_logic} {σ : genv}
           (this : Loc) (cls : globname) (f : obj_name)
           (Q : forall (faddr this_addr : ptr), mpred) : mpred :=
  Exists σ' mdc (pf : class_derives σ' mdc cls),
                (* ^ note that [class_compatible] (below) implies that this is
                   equivalent to [class_derives σ mdc cls] *)
    (Exists q, _at this (_instance_of σ' mdc cls q) **
               [| class_compatible σ.(genv_tu) σ'.(genv_tu) mdc |] ** ltrue) //\\
    match get_impl pf f with
    | Some (fa, off) =>
      Exists p, _offsetL off this &~ p ** Q fa p
    | None => (* the function wasn't found or the implemenation was pure virtual *)
      lfalse
    end.

Module TEST.
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

Definition t p : class_derives {| genv_tu:=module; glob_addr := fun x => Some (p x) ; pointer_size := 8|} "_Z1C" "_Z1A".
econstructor.
{ reflexivity. }
{ left; reflexivity. }
econstructor.
{ reflexivity. }
{ left; reflexivity. }
econstructor.
{ reflexivity. }
Defined.


(* Eval cbv beta iota zeta delta [ get_impl dispatch glob_addr fst ] in fun p => get_impl (t p) "_ZNK1A3fooEv"%bs. *)

End TEST.
