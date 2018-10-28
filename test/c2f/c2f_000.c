#include <stdio.h>
int main() {
  int x = 23;
  int y = 24;
  int z = ((x | y) <= (x & y)) + 3;
  int r = (x < y) ? 5 : ((x && y) + 2);
  printf("%d\n", z);
  return 0;
}
