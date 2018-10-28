#include <stdio.h>

int main() {
  int x = 2;
  float f = 3.9f + x;
  printf("%d\n", (int) f);
  printf("%d\n", (int) (f + 0.2f));
  return 0;
}
