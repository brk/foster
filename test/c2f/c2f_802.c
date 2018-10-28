#include <stdio.h>
int main() {
  printf("%d\n", (((1 << 1) << 1) ? 1 : 2));
  //printf("%d\n", ((!(!1 << 1) << 1) ? 3 : 4));
  printf("%d\n", (!1 + 2));
  printf("%d\n", (!0 + 2));
  printf("%d\n", (!-0 + 2));
  printf("%d\n", (!-1 + 2));
  printf("%d\n", (!(!1 + 1)));
  printf("%d\n", ((!(!1 + 1)) ? 5 : 6));
  printf("%d\n", (!0 ? 7 : 8));
  return 0;
}
