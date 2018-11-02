#include <stdio.h>

int foo(int x) {
  do {
    if (x <= 0) return 1;
    x -= 2;
  } while(1);
}

int main() {
  printf("%d\n", foo(3));
  return 0;
}
