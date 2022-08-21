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

Notes
-------

It requires a :cpp:`reinterpret_cast` to construct a pointer to the underlying memory of an object (for use with raw accesses). This seems to suggest that pointers must contain some bit of information regarding this.

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

Question: Do subobjects have names? They can be named by the complete object name and the path to the object (since this path is unique). Is this the same as a pointer?

Question: Pointer operations can not escape allocations, but they can "go up" through certain operations such as base-to-derived casts.
