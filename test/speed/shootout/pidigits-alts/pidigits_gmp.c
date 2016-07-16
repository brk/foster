#include "stdio.h"
#include "stdlib.h"
#include "string.h"
#include "gmp.h"

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
  mpz_t n, s, a, d, t, u, tmp;

  if (argc == 2) { N = atoi(argv[1]); }

  mp_init_value(V(n), 1);
  mp_init_value(V(s), 0);
  mp_init_value(V(a), 0);
  mp_init_value(V(d), 1);
  mp_init_value(V(t), 0);
  mp_init_value(V(u), 0);
  mp_init_value(V(tmp), 0);

  while (ii < N) {
    kk += 1;
    k1 += 2;
    mp_mul_pow2(V(n), 1, V(t)); // t = n * 2   (or mp_mul_value(V(n), 2, V(t));)
    mp_mul_value(V(n), kk, V(n)); // n *= k
    mp_add(V(a), V(t), V(a)); // a += t
    mp_mul_value(V(a), k1, V(a));
    mp_mul_value(V(d), k1, V(d));
    if (mp_ge(V(a), V(n))) {
      mp_mul_value(V(n), 3, V(tmp));
      mp_add(V(tmp), V(a), V(tmp));
      mp_div(V(tmp), V(d), V(t), V(u));
      mp_add(V(u), V(n), V(u));
      if (mp_gt(V(d), V(u))) {
        mp_mul_value(V(s), 10, V(s));
        mp_add(V(s), V(t), V(s));        // ns = ns*10  + t
        ii += 1;
        if (ii % 10 == 0) {
          print_pidigits(V(s), ii);
          mp_set_value(V(s), 0);
        }
        mp_mul(V(d), V(t), V(tmp));
        mp_sub(V(a), V(tmp), V(a));
        mp_mul_value(V(a), 10, V(a));
        mp_mul_value(V(n), 10, V(n));
      }
    }
  }

  return 0;
}

