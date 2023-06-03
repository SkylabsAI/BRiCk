struct C {
  int _x[10];
  static int foo() { return sizeof(_x); }
  static int bar() { return sizeof(&_x); }
};
