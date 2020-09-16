struct X {
  int x;
};


int test() {
  X x;
  X y;
  y = X();
  return x.x;
}
