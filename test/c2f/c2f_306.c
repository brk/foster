#include <stdio.h>

int main() {
  int foo[10], bar[10];
  bar[0] = 0xCC;
  bar[0] &= 234;
  printf("%d\n", bar[0]);
  return 0;
}
