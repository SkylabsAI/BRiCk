struct X {};

struct D {
  const X& c_;
  D(const X& c) : c_{c} {}
  ~D() { } // not trivially destructible
};
struct C { // trivially destructible
  const D& d;
};

struct DD {
  const X& c_;
  ~DD() { } // not trivially destructible
};
struct CC { // trivially destructible
  const DD& d;
};


int foo(const C&, const C&, const CC&, const CC&);

const int& id(const int& x) { return x; }

void test() {
  const C& x1 = C{D(X{})};    // C and D are extruded to x1. This uses [CXXConstructExpr]
  const C& x2 = C{D{X{}}};    // C and D are extruded to x2. This uses [CXXTempoaryObjectExpr] (a subclass of [CXXConstructExpr])

  const CC& x3 = CC{DD(X{})}; // CC and DD are extruded to x3. <D(...)> uses [CXXParenListInitExpr]
  const CC& x4 = CC{DD{X{}}}; // CC, DD, and X are all extruded to x4. <D{..}> uses [InitListExpr]

  foo(C{D{X{}}}, C{D(X{})}, CC{DD{X{}}}, CC{DD{X{}}});
  // ^^ <C>s and <CC>s are destroyed immediately b/c they are trivially destructible
  // ^^ D and CC are destroyed late, i.e. CC is extruded to the lifetime of D

  const int& y = id(1); // not-extruded
  const int& z = 1; // extruded
}
