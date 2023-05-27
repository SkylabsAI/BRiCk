struct C {
  int x;
  void foo();
  void bar() &;
  void baz() &&;
};

void test() {
  auto x = &C::x;
  const auto cx = &C::x;
  auto foo = &C::foo;
  auto bar = &C::bar;
  auto baz = &C::baz;
}
