#include <stdio.h>

int main() {
  int a, b;
  int* p = &a;
  int* q = &b;
  int* z = &a;
  printf("%d\n", (int)(p == q));
  printf("%d\n", (int)(p == z));
}
