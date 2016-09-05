#include <stdio.h>
int foo(int x) {
  if (x) {
    return 1;
  } else {
    return 2;
  }
}

int main() {
  printf("%d\n", foo(0));
  printf("%d\n", foo(1));
  return 0;
}
