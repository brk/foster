#include <stdio.h>
#include <stdint.h>

void p2() {
  uint16_t l_86 = 0;
  int l_87 = 0;
  int l_95 = 0;
  int l_8 = 0;
  int l_98 = 0;
  if (((int16_t)(((l_86 > 5U) | ((-(int32_t)((uint16_t)(l_86 || 0xDFE816D3) + (uint16_t)l_87)) < l_95)) == (-8)) >> (int16_t)l_8))
  { /* block id: 20 */
    l_98 = (~(!1));
  }
  else
  { /* block id: 22 */
    uint32_t l_99 = 0xFDFBAD29;
    int32_t l_100 = 0x8ADFEA02;
    if (l_99)
      return;
    l_100 = (0x4DBB < l_99);
    l_100 = (0x9BCB < l_98);
  }
  l_86 = 2;
}

int main() {
  int x = 1;
  if ((x == 1) || 1) { x++; }
  x = ((x == 1) || 1);


  if (x || 1) { x++; }
  x = (x || 1) + 1;
  x = (x || 1) ? 2 : 3;

  if (0) return 0;
  printf("%d\n", x);
  return 0;
}
