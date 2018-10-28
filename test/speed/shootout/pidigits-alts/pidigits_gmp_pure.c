#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include "gmp.h"

#define    mp_init              mpz_init
#define    mp_mul_value(n,k,t)  mpz_mul_si(t,n,k)
#define    mp_set_value         mpz_set_si
#define    mp_init_value(v,n)   mpz_init_set_si(v,n)
#define    mp_mul_pow2(n,k,t)   mpz_mul_2exp(t,n,k)
#define    mp_compare           mpz_cmp
#define    mp_to_string(a,b,c,d) mpz_out_str(a,c,b,d)
#define    mp_add(n,t,r)        mpz_add(r,n,t)
#define    mp_sub(n,t,r)        mpz_sub(r,n,t)
#define    mp_mul(n,t,r)        mpz_mul(r,n,t)
#define    mp_div(n,d,q,r)      mpz_tdiv_qr(q,r,n,d)

inline int mp_ge(mpz_t a, mpz_t b) {
  return mpz_cmp(a, b) >= 0;
}

inline int mp_gt(mpz_t a, mpz_t b) {
  return mpz_cmp(a, b) > 0;
}

void print_pidigits(mpz_t ns, int32_t i) {
  /*
  char buf[20];
  mp_to_string(ns, 10, &buf[0], 20);
  int padding_zeros = 10 - strlen(buf);
  while (padding_zeros --> 0) { printf("0"); }
  printf("%s\t:%d\n", &buf[0], i);
  */
  gmp_printf("%010Zd\t:%d\n", ns, i);
}

#define V(v) v

int main(int argc, char *argv[])
{
  int N = 1000;
  int ii = 0;
  int kk = 0;
  int k1 = 1;
  mpz_t n, n1, a, s, s0, s1, a1, d, t, u, u0, tmp0, tmp, tmp1, tmp2;
  mpz_t n0, d0, a0;

  if (argc == 2) { N = atoi(argv[1]); }

  mp_init_value(V(a0), 0);
  mp_init_value(V(n0), 1);
  mp_init_value(V(d0), 1);

  mp_init_value(V(a1), 0);
  mp_init_value(V(s0), 0);
  mp_init_value(V(s1), 0);
  mp_init_value(V(u0), 0);
  mp_init_value(V(n1), 0);
  mp_init_value(V(n), 1);
  mp_init_value(V(s), 0);
  mp_init_value(V(a), 0);
  mp_init_value(V(d), 1);
  mp_init_value(V(t), 0);
  mp_init_value(V(u), 0);
  mp_init_value(V(tmp), 0);
  mp_init_value(V(tmp0), 0);
  mp_init_value(V(tmp1), 0);
  mp_init_value(V(tmp2), 0);

#define clr(x,y) mpz_clear(x); mpz_swap(x,y)

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

