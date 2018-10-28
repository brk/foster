#include <stdio.h>
#include <inttypes.h>

int main() {
  int32_t x = 3;
  int64_t s = 0;
  int32_t z = 0;
  z = (x |= s);
  printf("%d\n", z);
  printf("%d\n", x);
  printf("%d\n", s);
  return 0;
}
