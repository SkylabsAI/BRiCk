#include <new>
#include <cstdio>
#include "redef_new.hpp"
using namespace std;

int main(void) {
  int* p = new int;
  bool res = (char*)p == storage;
  *p = 1;
  printf("Result: %d; *p %d, storage %d\n",
         res, *p, storage[0]);
  // printf("Result: %d; p %p, storage %p, *p %d, storage %d\n",
  //        res, p, storage, *p, storage[0]);
  printf("storage %p\n", storage);
}
