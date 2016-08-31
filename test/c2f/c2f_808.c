#include <stdio.h>
int foo(int argc) {
  int a = 0;
  switch(argc) {
    case 0:
      a = 1;
      a = 2;
      break;
    case 1:
      a = 3;
      a = 3;
    default:
      a = 5;
      break;
  }
  printf("%d\n", a);
  return 0;
}

int main() {
  foo(-1);
  foo(0);
  foo(1);
  foo(2);
}
