#include <stdio.h>
#include <stdint.h>

int main() {
  int32_t ix = -1;
  uint32_t ux = -1;
  printf("%d\n", ix);
  printf("%d\n", ux);
  printf("%d\n", (int16_t)(ix));
  printf("%d\n", (int16_t)(ux));
  printf("%d\n", (uint16_t)(ix));
  printf("%d\n", (uint16_t)(ux));
}
