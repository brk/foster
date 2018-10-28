#include <stdio.h>

struct foo { int bar; };

int main() {
  int a = 0;
  int* p = &a;
  struct foo f;
  struct foo* q = &f;
  printf("%d\n", (int)(p == NULL));
  printf("%d\n", (int)(q == NULL));
  printf("%d\n", (int)(q ? 1 : 2));
}
