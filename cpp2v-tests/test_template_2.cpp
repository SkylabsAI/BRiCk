#if 0
template<int X>
int value() { return X; }

template<typename T>
T get() { return T(); }
#endif

struct H { int x;
  int hash() const { return x; }
};

int hash(H x) {
  return x.x;
}

template<typename T>
int get_hash(const T& x) { return x.hash() + hash(x); }

template int get_hash<H>(const H&);


#if 0
template<template<typename> typename I>
I<int> foo() { return I<int>(5); }
#endif


