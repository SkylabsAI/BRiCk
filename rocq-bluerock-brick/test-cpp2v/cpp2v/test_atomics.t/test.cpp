/*
 * Copyright (C) BlueRock Security Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

void test() {
    int x = 0, y = 7, z = 8;
    __atomic_fetch_or(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_and(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_xor(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_add(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_fetch_sub(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_or_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_and_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_xor_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_add_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_sub_fetch(&x, 0, __ATOMIC_SEQ_CST);
    __atomic_exchange(&x, &y, &z, __ATOMIC_SEQ_CST);
    __atomic_exchange_n(&x, 0, __ATOMIC_SEQ_CST);
}
