/*
 * Copyright (C) BlueRock Security Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

extern "C" {
  int C_foo();
};


void foo();

void foo() { C_foo(); }
void foo(int i) { }
void foo(int i, int j) {}

enum class OneOf {
  A = 0,
  B = 1
};

class Q;
class P;

class P {
public:
  int go();
  Q* bar();
};

int P::go() { return 0; }
