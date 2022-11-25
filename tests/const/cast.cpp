
void foo (int * const x) {

  int * i = x;

  int const * j = x;

  int * const k = x;

  int const * const l = x;

  i = i;
  //i = j; discards qualifiers
  i = k;
  //i = l; discards qualifiers

  j = i;
  j = j;
  j = k;
  j = l;


  *i = *i;
  *i = *j;
  *i = *k;
  *i = *l;

  *k = *i;
  *k = *j;
  *k = *k;
  *k = *l;
}


