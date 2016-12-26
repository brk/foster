#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

typedef int64_t limb;

static void fsum(limb *output, const limb *in) {
  unsigned i;
  for (i = 0; i < 10; i += 2) {
    output[0+i] = output[0+i] + in[0+i];
    output[1+i] = output[1+i] + in[1+i];
  }
}

int main(void) {
  limb* a = (limb*) malloc(10 * sizeof(limb));
  limb* b = (limb*) malloc(10 * sizeof(limb));
  memset(a, 0, 10 *sizeof(limb));
  memset(b, 0, 10 *sizeof(limb));
  a[0] = 2; a[1] = 3; a[2] = 5; a[3] = 7;
  b[0] = 1; b[1] = 4; b[2] = 5; b[3] = 11;
  fsum(b, a);
  printf("%d\n", (int) b[0]);
  printf("%d\n", (int) b[1]);
  printf("%d\n", (int) b[2]);
  printf("%d\n", (int) b[3]);
  return 0;
}
