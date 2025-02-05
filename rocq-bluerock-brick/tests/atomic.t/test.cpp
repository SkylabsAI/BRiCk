_Atomic int foo() { return 1; }
_Atomic const int cfoo() { return 1; }
const _Atomic int ccfoo() { return 1; }

void test() {
  {
    auto x = foo();
    auto y = cfoo();
    auto z = ccfoo();

    int i = x;
    int j = y;
    int k = z;
  }

  {
    _Atomic int ax = 1;
    _Atomic const int ay = 1;
    const _Atomic int az = 1;
  }


}
