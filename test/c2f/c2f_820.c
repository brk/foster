#include <stdio.h>
int main() {
  int a = 0;
  int b = 0;
  int c = (b = ++a);
  int* pa = &a;
  int* pb = pa;

  c = (b = ++a);
/*
  if ((c = (b = ++a))) {
    ++b;
  } else {
    ++c;
  }
  */

  printf("%d\n", a);
  printf("%d\n", b);
  printf("%d\n", c);
}
