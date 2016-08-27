#include <stdio.h>

int foo(int x) { return x; }
int main() {
  printf("%d\n", foo(3 << 3));
}
