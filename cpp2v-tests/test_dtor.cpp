struct Y {
  int y;
};

struct X {
  int x;

  Y y;
};


int test() {
  X x;
  X y;
  y = X();
  return x.x;
}
