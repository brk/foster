#include <stdio.h>
int main() {
  int a = 0;
  for (int x = 0; x < 5; ++x) {
    if (x == 3) break;
    if (x == 1) continue;
    ++a;
  }
  printf("%d\n", a);
  return 0;
}
