#include <stdio.h>
#include <stdint.h>

int main() {
  uint16_t u = -22;
   int16_t su = -22;
  uint32_t b = u;
   int32_t s = u;
  printf("%d\n", b);
  printf("%d\n", s);
  printf("0x%X\n", b);
  printf("0x%X\n", s);

  printf("0x%X\n", 0xffea);
  printf("0x%X\n", 0xffffffea);

  uint32_t usu = su;
   int32_t ssu = su;
  printf("0x%X\n", usu);
  printf("0x%X\n", ssu);
  return 0;
}
