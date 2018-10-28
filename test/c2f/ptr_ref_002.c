#include <stdio.h>

int foo(int* x) { return *x; }

int bar(int a) { int* z = &a; --a; int b = *z; printf("%d\n", b); ++*z; return foo(z) + *z + b; }

int baz(int a) { int* z = &a; --a; int b = *z; printf("%d\n", b); ++*z; int* q1 = ++z; --z; return foo(z) + *z + b; }

int main() {
  printf("%d\n", bar(1));
  printf("%d\n", baz(2));
  return 0;
}
