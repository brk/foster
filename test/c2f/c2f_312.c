#include <stdio.h>
#include <string.h>
#include <stdint.h>

int foo(int x) {
  int a = 0;
  switch(x) {
  case 0: ++a;
  case 1: ++a; break;
  default: break;
  }
  return a;
}

int main() {
  printf("%d\n", foo(0));
  printf("%d\n", foo(1));
  printf("%d\n", foo(2));
  return 0;
}
