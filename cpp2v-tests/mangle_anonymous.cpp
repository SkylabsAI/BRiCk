typedef struct  {
  int y;
} X;

struct C {
  struct D {
    struct { struct { int kk; }; union { int ll; }; };
  };
  struct {
    int z;
    struct {
      int k;
    };
  } y;
  struct {
    int a;
  };
};

int
main(int, const char*[]){
	return 0;
}


enum {
  E = 3
};
