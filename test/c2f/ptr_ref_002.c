#include <stdio.h>

int foo(int* x) { return *x; }

int bar(int a) { int* z = &a; --a; ++*z; return foo(z) + *z; }

int baz(int a) { int* z = &a; --a; ++*z; int* q1 = ++z; --z; return foo(z) + *z; }

int main() {
  printf("%d\n", bar(0) + baz(0));
  return 0;
}
