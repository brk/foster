#include <stdio.h>

int f(int x) {
  return ++x ?: 42;
}

int main() {
  printf("%d\n", f(0));
  printf("%d\n", f(1));
  printf("%d\n", f(-1));
  return 0;
}
