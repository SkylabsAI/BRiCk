/*
 * Copyright (C) BedRock Systems Inc. 2019
 *
 * SPDX-License-Identifier:MIT-0
 */

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdalign.h>

int answer = 42;

typedef struct Type1 {
    int field1;
} Type1;
Type1 obj1 = {1};

typedef struct Type2 {
  int* field2;
} Type2;
Type2 obj2 = {&answer};

typedef int Type3;
Type3 obj3 = 2;

typedef unsigned char uchar;

size_t size_max(size_t a, size_t b) {
    return a < b ? b : a;
}

void
alloc_test() {
    //XXX non-generally-robust handling of alignment!
    printf("Sizeof %zd %zd %zd\n", sizeof(Type1), sizeof(Type2), sizeof(Type3));
    printf("Alignof %zd %zd %zd\n", alignof(Type1), alignof(Type2), alignof(Type3));

    //size_t size1 = sizeof(obj1); // causes UB below.
    size_t size1 = size_max(sizeof(obj1), alignof(Type2));
    size_t size2 = sizeof(obj2);
    size_t size3 = sizeof(obj3);
    //
    size_t totalSize = size1 + size2 + size3;
    uchar* ptrA = (uchar*)malloc(totalSize);
    uchar* ptrAOrig = ptrA;

    memcpy(ptrA, &obj1, sizeof(obj1));
    Type1* s1AP = (Type1*)ptrA;
    ptrA += size1;

    memcpy(ptrA, &obj2, sizeof(obj2));
    Type2* s2AP = (Type2*)ptrA; //UB here if size1 is < alignof(Type2).
    ptrA += size2;

    memcpy(ptrA, &obj3, sizeof(obj3));
    Type3* s3AP = (Type3*)ptrA;
    ptrA += size3;

    uchar* ptrB = (uchar*)malloc(totalSize);
    uchar* ptrBOrig = ptrB;
    memcpy(ptrB, ptrAOrig, totalSize);

    Type1* s1BP = (Type1*)ptrB;
    ptrB += size1;
    Type2* s2BP = (Type2*)ptrB;
    ptrB += size2;
    Type3* s3BP = (Type3*)ptrB;
    ptrB += size3;

    assert(s1BP->field1 == 1);
    assert(*s2BP->field2 == 42);
    assert(*s3BP == 2);
    printf("%d %d %d\n", s1BP->field1, *s2BP->field2, *s3BP);
}

int main(void) {
    alloc_test();
}
