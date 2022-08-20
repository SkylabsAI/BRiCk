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

Despite the fact that the pointers compare equal, the write to :cpp:`c.x[2]` is still illegal.

Example 2
===========

.. code-block:: cpp

   struct C { byte x[2]; byte y[2]; } c;

   byte* p = c.x;
   byte* px = static_cast<byte*>(&c); // `p` and `px` are the same pointer?
   px[2]; // legal
   c.x[2]; // also legal?

   if (c.x + 2 == c.y)
     c.x[2] = 0; // writes to c.y[0]

Discussion
-----------

.. topic:: Warning

   speculative



Example 3 -- Placement `new` and Provides Storage
===================================================

.. code-block:: cpp

   byte x[100];
   byte* p = new (static_cast<void*>(x)) byte[2];

   p[2]; // defined?

Discussion
-----------

.. topic:: Warning

   speculative

It is legal to index :cpp:`x[2]`. Normally, placement :cpp:`new` creates new provenance (a new allocation id), but in this case we have transparent replacability

Example 4 -- Placement `new` and Provides Storage (without transparent replacability)
=======================================================================================

.. code-block:: cpp

   struct C { byte x[2]; };
   byte x[100];
   C* pc = new (static_cast<void*>(x)) C();

   byte* b = static_cast<byte*>(pc); // is `b` the same as `x`?
   b[2]; // is this defined?

Discussion
------------

.. topic:: Warning

   speculative

Unlike the above example, placement :cpp:`new` does not apply because we are creating a :cpp:`struct`; however, the :cpp:`struct` contents is a :cpp:`byte` array.

Example 5
===========

.. code-block:: cpp

   struct C { int buf[2]; byte x[2]; } c;

   static_assert(offsetof(C, x) == 2 * sizeof(int));


   c.x[-offsetof(C, x)] // derive the head pointer from a field
   static_cast<byte*>(&c); // derive the root pointer from the root object
   static_cast<byte*>(c.buf); // derive the root pointer from the first field (see Example 1)
