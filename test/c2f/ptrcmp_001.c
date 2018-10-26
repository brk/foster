#include <stdio.h>

int main() {
  int a = 2, b = 3;
  int* p = &a;
  int* q = &b;
  int* z = &a;
  printf("%d\n", (int)(p == q));
  printf("%d\n", (int)(p == z));
  printf("%d\n", a);
  printf("%d\n", *q);
}
