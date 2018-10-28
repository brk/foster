#include <stdio.h>
int foo(int argc) {
  int a = 0;
  switch(argc) {
    case 0:
      a = 1;
      a = 2;
      break;
    case 1: {
      a = 3;
      break;
            }
    default:
      a = 5;
      break;
  }
  return a;
}

int main() {
  printf("%d\n", foo(0));
  printf("%d\n", foo(1));
  printf("%d\n", foo(2));
  return 0;
}

