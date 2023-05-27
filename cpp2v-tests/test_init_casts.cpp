/*
 * Copyright (c) 2023 BedRock Systems, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */

struct C {};

const C mk_cc() { return C{}; }
C mk_c() { return C{}; }

void test() {
        C   x0  = C{};
  const C   x1{};
  const C   x2  = C{};
        C   x3  = mk_c();
  const C   x4  = mk_c(); // cast which adds const
        C   x5  = mk_cc(); // cast which removes const
  const C   x6  = mk_cc();
#if 0	// avoid scope extrusion error
  const C&  x7  = mk_c();
  const C&  x8  = mk_cc();
  const C&& x9  = mk_c();
  const C&& x10 = mk_cc();
#endif
}

extern void foo(const C c, C cc);

void test2() {
  foo(mk_c(), // nothing
      mk_cc()); // remove const
  foo(mk_cc(), // remove const
      mk_c()); // nothing

}

struct D : public C {};

void test3() {
  D d;
  static_cast<void>(static_cast<C&>(d)); // derived2base cast
  C c;
  static_cast<void>(static_cast<D&>(c)); // base2derived cast
}
