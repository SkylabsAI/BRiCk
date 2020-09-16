class C {

private:
  int x;
};

class D {
  D(const D&) = delete;
  D(D&) = delete;
  D& operator=(const D&) =delete;
  D& operator=(D&) = delete;
private:
  int x;
};
