#include <stdio.h>

int foo(int* x) { return *x; }

int bar(int a) { return foo(&a); }

int main() {
  printf("%d\n", bar(0));
  return 0;
}
