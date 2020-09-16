#if 0
struct S { int x; };

int testS() { return S().x; }
#endif
struct T { int x; };

int testT() {
  T x;
  return x.x;
}

struct U { int x; };

int testU() {
  U x;
  x = U();
  return x.x;
}

struct V { int x; };

struct W { int x; ~W() = default; };

int testW() {
  W x;
  x = W();
  return x.x;
}

struct X { int x; ~X() {} };

int testX() {
  X x;
  return  x.x;
}

