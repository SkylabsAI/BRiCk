/*
 * Copyright (C) BlueRock Security Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

template<int X>
class T {
  //Clang produces different ASTs on this code in C++14 and C++17
  //(in 17, there's no initializer for Y (= 42) in the specialized
  //class foo below).
  static constexpr int Y = X;
};
T<42> foo;
