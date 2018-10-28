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
#define    swp(x,y)             mpz_swap(x,y);
#define    clr(x,y)             swp(x,y); mpz_clear(y)
#define    mp_size_base2(x)     mpz_sizeinbase(x, 2)
#define V(v) v
#define mp_int_t mpz_t

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

int main(int argc, char *argv[])
{
  size_t N = 1000, iters = 0;
  mp_int_t x, y, t1, t2;

  if (argc == 2) { N = atoi(argv[1]); }

  mp_init_value(V(x), 1);
  mp_init_value(V(y), 2);
  mp_init_value(V(t1), 0);
  mp_init_value(V(t2), 0);

  while (mp_size_base2(V(x)) < N) {
    //printf("%6d: ", iters); mp_fwrite(&x, 10, stdout); printf("\n");
    //printf("%6d: %d\n", iters, mp_count_bits(&x));
    mp_add(V(x), V(y), V(t1));
    mp_add(V(t1),V(y), V(t2));
    swp(V(x), V(t1));
    swp(V(y), V(t2));
    //mpz_clear(V(t1));
    //mpz_clear(V(t2));
    ++iters;
  }

  printf("%d\n", iters);

  return 0;
}

