#include <string.h>
#include <stdio.h>
#include <stdint.h>

int main() {
  int foo[3] = { 1, 2, 3 };
  int bar[3];

  memcpy(bar, foo, sizeof(int) * 3);

  printf("%d\n", bar[0]);
  printf("%d\n", bar[1]);
  printf("%d\n", bar[2]);

  return 0;
}
