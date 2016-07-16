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
  mp_int n, n0, n1, s, s0, s1, a, a0, a1, d, d0, t, u, u0, tmp, tmp0, tmp1, tmp2;



#define V(v) &v

  if (argc == 2) { N = atoi(argv[1]); }

  mp_init_value(&n, 1);
  mp_init_value(&n0, 1);
  mp_init_value(&n1, 0);
  mp_init_value(&s, 0);
  mp_init_value(&s0, 0);
  mp_init_value(&s1, 0);
  mp_init_value(&a, 0);
  mp_init_value(&a0, 0);
  mp_init_value(&a1, 0);
  mp_init_value(&d, 1);
  mp_init_value(&d0, 1);
  mp_init_value(&t, 0);
  mp_init_value(&u, 0);
  mp_init_value(&u0, 0);
  mp_init_value(&tmp, 0);
  mp_init_value(&tmp0, 0);
  mp_init_value(&tmp1, 0);
  mp_init_value(&tmp2, 0);

#define clr(x,y) mp_clear(V(x)); mp_copy(V(y),V(x))

  while (ii < N) {
    kk += 1;
    k1 += 2;
    mp_mul_value(V(n0), kk, V(n)); // n = n0 * k
    mp_mul_pow2(V(n0), 1, V(t));   // t = n0 * 2
    mp_add(V(a0), V(t), V(a1));    // a1 = a0 + t
    mp_mul_value(V(a1), k1, V(a)); // a = a1 * k1
    mp_mul_value(V(d0), k1, V(d)); // d = d0 * k1
    if (mp_ge(V(a), V(n))) {
      mp_mul_value(V(n), 3, V(tmp0));
      mp_add(V(tmp0), V(a), V(tmp1));
      mp_div(V(tmp1), V(d), V(t), V(u0));
      mp_add(V(u0), V(n), V(u));
      if (mp_gt(V(d), V(u))) {
        mp_mul_value(V(s0), 10, V(s1));
        mp_add(V(s1), V(t), V(s));        // ns = ns*10  + t
        ii += 1;
        if (ii % 10 == 0) {
          print_pidigits(V(s), ii);
          mp_set_value(V(s), 0);
        }
        mp_mul(V(d), V(t), V(tmp2));
        mp_sub(V(a), V(tmp2), V(a1));
        mp_mul_value(V(a1), 10, V(a));
        mp_mul_value(V(n), 10, V(n1));

        clr(s0, s);
        clr(n, n1);
      }
    }
    clr(n0, n);
    clr(a0, a);
    clr(d0, d);
  }

  return 0;
}

