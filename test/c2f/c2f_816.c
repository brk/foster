#include <stdio.h>

int main() {
  int x = 0;
  for (x = 0; x < 3; ++x) {
    int a = 22;
    printf("%d\n", a);
    if (a == 2342) break;
    a = 1;
  }
  printf("%d\n", x);
  return 0;
}
