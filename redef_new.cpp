#include <new>
#include <cstdio>
using namespace std;
char storage[2*sizeof(int)];

void *operator new(size_t size) throw(std::bad_alloc) {
  printf("new's return value %p\n", storage);
  return storage;
}

