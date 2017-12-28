#include <stdio.h>

struct foo { int x[3]; };

int main() {
  struct foo f;
  f.x[0] = 42;
  printf("%d\n", f.x[0]);
}
