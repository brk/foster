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
  int N = 1000;
  int ii = 0;
  int kk = 0;
  int k1 = 1;
  mp_int n, s, a, d, t, u, tmp;

  if (argc == 2) { N = atoi(argv[1]); }

  mp_init_value(&n, 1);
  mp_init_value(&s, 0);
  mp_init_value(&a, 0);
  mp_init_value(&d, 1);
  mp_init_value(&t, 0);
  mp_init_value(&u, 0);
  mp_init_value(&tmp, 0);

  while (ii < N) {
    kk += 1;
    k1 += 2;
    mp_mul_pow2(&n, 1, &t); // or mp_mul_value(&n, 2, &t);
    mp_mul_value(&n, kk, &n); // n *= k
    mp_add(&a, &t, &a); // a += t
    mp_mul_value(&a, k1, &a);
    mp_mul_value(&d, k1, &d);
    if (mp_ge(&a, &n)) {
      mp_mul_value(&n, 3, &tmp);
      mp_add(&tmp, &a, &tmp);
      mp_div(&tmp, &d, &t, &u);
      mp_add(&u, &n, &u);
      if (mp_gt(&d, &u)) {
        mp_mul_value(&s, 10, &s);
        mp_add(&s, &t, &s);        // ns = ns*10  + t
        ii += 1;
        if (ii % 10 == 0) {
          print_pidigits(&s, ii);
          mp_set_value(&s, 0);
        }
        mp_mul(&d, &t, &tmp);
        mp_sub(&a, &tmp, &a);
        mp_mul_value(&a, 10, &a);
        mp_mul_value(&n, 10, &n);
      }
    }
  }

  return 0;
}

