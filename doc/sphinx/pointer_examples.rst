.. _pointer-examples:

###############################
Pointer Examples
###############################

Example 1
============

.. code-block:: cpp

   struct C { int x[2]; int y[2]; } c;

   int* pcx = static_cast<int*>(c.x);
   int* px  = c.x;
   byte* b  = static_cast<byte*>(&c);

   if (c.x + 2 == c.y)
      c.x[2] = 0; // undefined behavior

Discussion
------------

Despite the fact that the pointers compare equal, the write to :cpp:`c.x[2]` is still illegal. See `[basic.compound]<https://eel.is/c++draft/basic.compound#note-2>`_.

(This is based on an example in Cerberus, ...link required...)

Example 2
===========

.. code-block:: cpp

   struct C { byte x[2]; byte y[2]; } c;

   byte* p = c.x;
   byte* pr = reinterpret_cast<byte*>(&c); // pointer to raw object
   byte* px = static_cast<byte*>(&c); // ??
   pr[2]; // legal because `pr` is a pointer to the raw representation
   assert(pr + 2 == c.x + 2);
   // ^ guaranteed due to the layout of arrays (citation...)
   // and the fact that there is no leading padding (citation...)

   c.x[2]; // illegal [basic.compound]


Example 3 -- Placement `new` and Provides Storage
===================================================

.. code-block:: cpp

   byte x[100];
   byte* p = new (static_cast<void*>(x)) byte[2];

   p[2]; // undefined because subscripting can not leave the range of an allocation.

Example 4 -- Placement `new` and Provides Storage (without transparent replacability)
=======================================================================================

.. code-block:: cpp

   struct C { byte x[2]; };
   byte x[100];
   C* pc = new (static_cast<void*>(x)) C();

   byte* b = static_cast<byte*>(pc); // `b` is still part of the allocation for `pc`
   b[2]; // undefined.


Example 5
===========

.. code-block:: cpp

   struct C { int buf[2]; byte x[2]; } c;

   static_assert(offsetof(C, x) == 2 * sizeof(int));

   c.x[-offsetof(C, x)] // derive the head pointer from a field
   static_cast<byte*>(&c); // derive the root pointer from the root object
   static_cast<byte*>(c.buf); // derive the root pointer from the first field (see Example 1)

**Question**: Is it possible to get to the underlying bytes from a field of type :cpp:`byte`?

**Answer**: We believe the answer is "no", that getting to the underlying bytes *requires* a :cpp:`reinterpret_cast`.

**Consequence**: What information within the pointer records whether it was derived via a :cpp:`reinterpret_cast` that could access the raw representation? Parts of the stand suggest that certain operations (e.g. cast to :cpp:`void*`) do not change the value of the pointer (`[conv.ptr#2]<https://eel.is/c++draft/conv.ptr#2>`_).


Example 6
==========

.. code-block:: cpp

   struct C { byte x; };
   struct D { C c[2]; } d;

   byte* r1 = reinterpret_cast<byte*>(&(d.c[0].x)); // `reinterpret_cast` gets to the raw representation
   byte* r2 = r1 + sizeof(C); // defined because we are working with the raw representation
   assert(r2 == reinterpret_cast<byte*>(d.c + 1)); // by class and array layout
   *r2 = 0; // defined, same as `d.c[1].x = 0`
            // the raw representation is bound only by the complete object, not by the sub-object

   byte* p1 = static_cast<byte*>(&(d.c[0].x)); // `static_cast` is a no-op here
   byte* p2 = p1 + sizeof(C); // undefined

Discussion
-----------

It seems necessary to track whether a pointer is working with the raw representation or with the "structured" representation. This could be represented as :coq:`alloc_id * (path + Z)`. Another option would be :coq:`alloc_id * path * option Z` but this seems to contain unnecessary information if the comment on line 8 is correct.
