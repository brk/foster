#include <stdio.h>
int main() {
  printf("%d\n", (-0 ? 1 : 2));
  printf("%d\n", (-(0 + 0) ? 3 : 4));
  return 0;
}
