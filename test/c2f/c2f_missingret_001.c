#include <stdio.h>

int f(int x) {
  if (x == 0) {
    return 1;
  }

  return 2;
}

int main() {
  printf("%d\n", f(0));
  printf("%d\n", f(7));
  return 0;
}
