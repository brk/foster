#include <stdio.h>
#include <stdint.h>

int foo(int a) {
  if (a) {
    a += 2;
  } else {
    a += 3;
  }
  return a;
}
int main() {
  printf("%d\n", foo(0));
  printf("%d\n", foo(1));
  printf("%d\n", foo(-1));
  uint16_t p4 = -19;
  printf("%d\n", p4 == -19);
  printf("%d\n", p4 == (uint16_t)-19); p4 += 9;
  printf("%d\n", p4 == -10);
  printf("%d\n", p4 == (uint16_t)-10); p4 += 9;
  printf("%d\n", p4 == -1);
  printf("%d\n", p4 == (uint16_t)-1); p4 += 9;
  printf("%d\n", p4 == 8);
  printf("%d\n", p4 == (uint16_t)8); p4 += 9;
  return 0;
}
