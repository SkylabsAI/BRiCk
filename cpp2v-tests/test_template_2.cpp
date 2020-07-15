template<int X>
int value() { return X; }

template<typename T>
T get() { return T(); }

template<typename T>
int get_hash(const T& x) { return x.hash() + hash(x); }

template<template<typename> typename I>
I<int> foo() { return I<int>(5); }
