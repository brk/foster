#include <stdio.h>
int foo(int argc) {
  switch (argc) {
    case 1: return 1;
    case 2:
    case 3:
      return 2;
    case 4:
      goto yy6;
    case 5:
      break;
    default:
      return 6;
  }
yy6:
  return 0;
}

int main() {
  printf("%d\n", foo(0));
  printf("%d\n", foo(1));
  printf("%d\n", foo(2));
  printf("%d\n", foo(3));
  printf("%d\n", foo(4));
  printf("%d\n", foo(5));
  printf("%d\n", foo(6));
  return 0;
}
