.. _cpp_pointers:

##################################
The C++ Pointer Model
##################################

This page provides an annotated list of the properties of the C++ pointer model.

- two _objects_ are *pointer-interconvertible* (`[basic.compound#4]<https://eel.is/c++draft/basic.compound#4>`_)
  - "If two objects are pointer interconvertible, then they have the same address and it is possible to obtain a pointer to one from a pointer to the other via a :cpp:`reinterpret_cast`.
  - this is reflexive and transitive (and symmetric)
  -
- *reachable byte* (`[basic.compound#5]<https://eel.is/c++draft/basic.compound#5>`_)
- *provides storage* (`[intro.object-3]<https://eel.is/c++draft/basic.memobj#intro.object-3>`_).
  "The array provides storage for the created object."
- "every value of pointer type is one of the following" (see `[basic.compound-3]<https://eel.is/c++draft/basic.types#basic.compound-3>`_)
  - pointer to an object of function
  - pointer to past the end of an object
  - *the* null pointer value *for that type*
  - an invalid pointer value
- Quoting the standard:
  > The value representation of pointer types is implementation-defined. Pointers to layout-compatible types shall have the same value representation and alignment requirement

The C++ Memory Model
======================

See the standard: `[intro.memory]<https://eel.is/c++draft/intro.memory>`_.

- Objects `[intro.object-1]<https://eel.is/c++draft/basic.memobj#intro.object-1>`_.
  "The constructs in a C++ program create, destroy, refer to, access, and manipulate objects."
- Subobjects `[intro.object-2]<https://eel.is/c++draft/basic.memobj#intro.object-2>`_.
  These include: members, base class subobjects, or an array element.
  - Every subobject has a unique parent.
- Complete object is an object that is not a subobject.
- Replacing a subobject (see `[intro.object-2]<https://eel.is/c++draft/basic.memobj#intro.object-2>`_).
- Nested within (see `[intro.object-4]<https://eel.is/c++draft/basic.memobj#intro.object-4>`_).
- potentially-overlapping subobject (see `[intro.object-7]<https://eel.is/c++draft/basic.memobj#intro.object-7>`_).
  Question: where is this useful? Proposed answer: It gives flexibility to overlap base classes for mixins.
- the address f an object (if it is not zero-size) is the address of the first byte that it occupies.

- "A byte of storage is reachable through a pointer" (see `[basic.compound-5]<https://eel.is/c++draft/basic.types#basic.compound-5>`_)
  > A byte of storage b is reachable through a pointer value that points to an object x if there is an object y, pointer-interconvertible with x, such that b is within the storage occupied by y, or the immediately-enclosing array object if y is an array element.

Notes
------

Memory being an array of bytes seems like the intended model; however, there needs to be locations that are not truly virtual addresses.
Additional structure, e.g. "provides storage", subobjects, types, etc, are described as a separate layer.

Question: Are allocation ids the "names of complete objects"?

Question: Do subobjects have names? They can be named by the complete object name and the path to the object (since this path is unique).

Question: Pointer operations can not escape allocations, but they can "go up" through certain operations such as base-to-derived casts.


Strawman Model
===============

.. code-block:: coq

  (* storage *)
  (* C++ storage addresses
     These are distinct from (but similar to) machine addresses.
   *)
  Parameter saddr : Set.
  (* the storage state of the C++ abstract machine *)
  Definition storage : Set := map saddr byte.


  (* object names *)
  Parameter alloc_id : Set.
  Variant path : Set :=
  | o_base (_ _ : globname)
  | o_field (_ : globname) (_ : ident)
  | o_sub (_ : type) (_ : N). (* still some oddity around [o_sub _ 0] *)
  Definition object_name := alloc_id * list path.

  Parameter alloc_type : alloc_id -> type.

  (* the type of an allocation
     NOTE: this is only a deterministic function if the type
           is included somewhere (because any pointer can be a pointer to
           the beginning of its raw bytes).
   *)
  #[local]
  Fixpoint object_type_from (ty : type) (ps : list path) : option type :=
    match ps with
    | [] => Some ty
    | p :: ps =>
      match p with
      | o_field cls f =>
        (* Q: if [ty = Tarray (Tnamed base) _], is this valid?
           - this is necessary if [o_sub ty 0] is an identity
           - this precludes "a pointer to an array is not inter-convertible
             to its first member" (since inter-convertible should be reflexive)
         *)
        if bool_decide (ty = Tnamed cls)
        then ty' <- type_of_field cls f ;
             object_type_from ty' ps
        else ∅
      | o_base base derived =>
        (* Q: same as above *)
        if bool_decide (ty = Tnamed base)
        then object_type_from (Tnamed derived) ps
        else ∅
      | o_sub t n =>
        match ty with (* this does not work for matricies *)
        | Tarray t _ =>
          if bool_decide (ty = t)
          then object_type_from t ps
          else ∅
        | ty' =>
          if bool_decide (ty = ty')
          then object_type_from t ps
          else ∅
        end
      end
    end.

  (* the type of an object *)
  Definition object_type (o : object_name) : option type :=
    object_type_from (alloc_type o.1) o.2.

  Variant ptr : Set :=
  | p_structured (obj : object_name) (off : Z)
    (* ^ valid when the [off] is compatible with [alloc_type(alloc)]
      the type is the "natural" one
    *)
  | p_null       (_ : type)
  | p_invalid
  .

  Definition ptr_type (p : ptr) : option type :=
    match p with
    | p_structured obj off =>
      match object_type obj with
      | None => { }
      | Some ty =>
        if bool_decide (off = 0)
        then { ty } ∪ { byte } (* <-- this does not work *)
        else Some byte
      end
    | p_null ty => Some ty
    | p_invalid => None
    end.

  (* both validity and strict validity are defined with types, i.e.
    - [valid_ptr ty p]
    - [valid_ref ty p] ~ equivalent to [type_ptr ty p]

    [{,strict_}valid_ptr ty p |-- {,strict_}valid_ptr (Tptr Tvoid) p]
  *)

  (* a [reinterpret_cast<byte*>(p)] *allows* you to convert a structured
    pointer to a raw pointer.
    a [reinterpret_cast<T*>((byte*)r)] applies to both structured and raw
    pointers.
    - if [r = p_raw alloc off], then you can construct any *valid* pointer
      [p_structured alloc off'] such that [off = eval_offset off'] and
      [off'] is compatible with [alloc_type(alloc)].
    - if [r = p_structured alloc off], then you can construct any *valid* pointer
      [p_structured alloc off'] based on "pointer interconvertible" and
      [eval_offset off = eval_offset off'] and [off'] is compatible with
      [alloc_type(alloc)].
  *)
