struct D {
  ~D() {}
  int x;
};

struct C {
  D d;
  int x;
};

void foo(C& x) {
  x.~C();
}
