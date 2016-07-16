#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include "tommath.h"

#define    mp_mul_value         mp_mul_d
#define    mp_set_value         mp_set_int
#define    mp_init_value(v,n)   mp_init(v); mp_set_int(v,n)
#define    mp_mul_pow2          mp_mul_2d
#define    mp_compare           mp_cmp
#define    mp_to_string(a,b,c,d) mp_toradix_n(a,c,b,d)
#define    mp_size_base2(x)     mp_count_bits(x)

#define    swap(x,y)            mp_exch(x,y)
// result: swap x and y; new y is cleared.
#define    clr(x,y)             mp_clear(x); swap(x,y)

inline int mp_ge(mp_int* a, mp_int* b) {
  return mp_compare(a, b) >= 0;
}

inline int mp_gt(mp_int* a, mp_int* b) {
  return mp_compare(a, b) > 0;
}

void print_pidigits(mp_int* ns, int32_t i) {
  char buf[20];
  mp_to_string(ns, 10, &buf[0], 20);
  int padding_zeros = 10 - strlen(buf);
  while (padding_zeros --> 0) { printf("0"); }
  printf("%s\t:%d\n", &buf[0], i);
}

int main(int argc, char *argv[])
{
  int N = 1000, iters = 0;
  mp_int x, y, t1, t2;

  if (argc == 2) { N = atoi(argv[1]); }

  mp_init_value(&x, 1);
  mp_init_value(&y, 2);
  mp_init_value(&t1, 0);
  mp_init_value(&t2, 0);

  while (mp_count_bits(&x) < N) {
    //printf("%6d: ", iters); mp_fwrite(&x, 10, stdout); printf("\n");
    //printf("%6d: %d\n", iters, mp_count_bits(&x));
    mp_add(&x, &y, &t1);
    mp_add(&t1, &y, &t2);
    clr(&x, &t1);
    clr(&y, &t2);
    ++iters;
  }

  printf("%d\n", iters);

  return 0;
}

