#include <stdio.h>
#include <stdint.h>

typedef int64_t limb;
typedef int32_t s32;


static inline limb
div_by_2_25(const limb v)
{
  /* High word of v; no shift needed*/
  const uint32_t highword = (uint32_t) (((uint64_t) v) >> 32);
  /* Set to all 1s if v was negative; else set to 0s. */
  const int32_t sign = ((int32_t) highword) >> 31;
  /* Set to 0x1ffffff if v was negative; else set to 0. */
  const int32_t roundoff = ((uint32_t) sign) >> 7;
  /* Should return v / (1<<25) */
  return (v + roundoff) >> 25;
}

static s32 s32_eq(s32 a, s32 b) {
  a = ~(a ^ b);
  a &= a << 16;
  a &= a << 8;
  a &= a << 4;
  a &= a << 2;
  a &= a << 1;
  return a >> 31;
}

static void
swap_conditional(limb a[19], limb b[19], limb iswap) {
  unsigned i;
  const s32 swap = (s32) -iswap;

  for (i = 0; i < 10; ++i) {
    const s32 x = swap & ( ((s32)a[i]) ^ ((s32)b[i]) );
    a[i] = ((s32)a[i]) ^ x;
    b[i] = ((s32)b[i]) ^ x;
  }
}

int main() {
  printf("%d\n", (int) div_by_2_25(0));
  printf("%d\n", (int) div_by_2_25(1 << 23));
  printf("%d\n", (int) div_by_2_25(1 << 24));
  printf("%d\n", (int) div_by_2_25(1 << 25));
  printf("%d\n", (int) div_by_2_25(1 << 26));
  printf("%d\n", (int) div_by_2_25(1 << 27));
  printf("%d\n", s32_eq(0, 0));
  printf("%d\n", s32_eq(0, 1));
  printf("%d\n", s32_eq(1, 1));
  printf("%d\n", s32_eq(1, 0));
  printf("%d\n", s32_eq(0xABCDEF, 0xABCDEF));
  printf("%d\n", s32_eq(0xABCDFE, 0xABCDEF));

  s32 foo[10];
  s32 baz[10] = {};
  s32 bar[10] = { 1 };

  printf("%d\n", bar[0] + 0);
  printf("%d\n", bar[1] + 0);
  printf("%d\n", baz[0] + 0);

  return 0;
}
