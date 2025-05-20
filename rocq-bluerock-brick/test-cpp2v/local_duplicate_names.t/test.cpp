void test() {
  using T = int;
  T x0;
  { using T = char;
    T x1;
    { struct T {}; T x2; }
    { struct T {}; T x3; }
  }
  { using T = long long; T x4; }
  T x5;
}
