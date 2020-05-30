Require Import bedrock.lang.cpp.ast.
Require Import bedrock.lang.cpp.semantics.
Require Import bedrock.lang.cpp.logic.path_pred.
Require Import bedrock.lang.cpp.logic.pred.
Require Import stdpp.fin_maps.
Require Import bedrock.lang.cpp.parser.

Section extends.
  Context (σ : genv).

  (** [dispatch mdc f] states that [f] is the name pointer and the fixup offset
      for a call to [f] on an object of type [obj] whose most-derived
      class is [mdc].
   *)
  Inductive class_derives (mdc : globname) : globname -> Set :=
  | Derives_here {st}
      {_ : σ.(genv_tu).(globals) !! mdc = Some (Gstruct st)}
    : class_derives mdc mdc

  | Derives_base base {st li result}
      {_ : σ.(genv_tu).(globals) !! mdc = Some (Gstruct st)}
      {_ : In (base, li) st.(s_bases)}
      (_ : class_derives base result)
    : class_derives mdc result

  (* this could be extended for virtuals *)
  .

  Section dispatch.
    Context `{Σ : cpp_logic}.
    Context (final : obj_name).

    Definition list_get {T} (t : obj_name) (l : list (obj_name * T)) : option T :=
      match List.find (fun '(t',_) => if decide (t = t') then true else false) l with
      | None => None
      | Some (_, k) => Some k
      end.

    Fixpoint dispatch `(d : class_derives mdc from)
      : (option obj_name * Offset (* from -> cls with obj_name *)) *
        (obj_name * Offset (* from -> mdc *)) :=
      match d with
      | @Derives_here _ st _ =>
        ((mjoin (list_get final st.(s_virtuals)), _id), (final, _id))
      | @Derives_base _ base st _ _ _ _ d =>
        let '(result, (cand, full)) := dispatch d in
        let full_path := _dot full (_derived σ base mdc) in
        match list_get cand st.(s_overrides) with
        | None => (result, (cand, full_path))
        | Some cand =>
          ((mjoin (list_get cand st.(s_virtuals)), full_path),
           (cand, full_path))
        end 
      end.
  End dispatch.

  Definition get_impl `{Σ : cpp_logic} `(r : class_derives mdc tcls) (f : obj_name)
    : option (ptr * Offset) :=
    let '(sym, off) := (dispatch f r).1 in
    match sym with
    | None => None
    | Some s => match glob_addr σ s with
               | None => None
               | Some p => Some (p, off)
               end
    end.

End extends.

Module TEST.

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

Arguments get_impl {_ _ _ _ _} _ _.

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

Eval compute in fun p => get_impl (t p) "_ZNK1A3fooEv"%bs.
