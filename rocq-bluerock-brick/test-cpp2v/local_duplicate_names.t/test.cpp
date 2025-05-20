void test() {
  using T = int;
  { using T = char;
    { using T = bool; }
    { using T = short; }
  }
  { using T = long long; }
}
