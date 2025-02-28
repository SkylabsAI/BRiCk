/*
 * Copyright (C) BlueRock Security Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

void test() {
    int t, desired, expected, value;

    __atomic_store_n(&t, value, __ATOMIC_SEQ_CST);
    __atomic_load_n(&t, __ATOMIC_SEQ_CST);
    __atomic_exchange_n(&t, value, __ATOMIC_SEQ_CST);
    __atomic_compare_exchange_n(&t, &expected, desired,
                                true, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
    __atomic_fetch_add(&t, value, __ATOMIC_SEQ_CST);
    __atomic_add_fetch(&t, value, __ATOMIC_SEQ_CST);
    __atomic_fetch_sub(&t, value, __ATOMIC_SEQ_CST);
    __atomic_sub_fetch(&t, value, __ATOMIC_SEQ_CST);


}
