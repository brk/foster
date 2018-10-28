#include <stdio.h>
int main() {
  int x = 23;
  int y = 24;
  int z = (3 ? ('x' ? 1 : 2) : ("foo" ? 3 : 4));
  int r = (x < y) ? 5 : ((x && y) + 2);
  printf("%d\n", x + y + z + r);
  return 0;
}
