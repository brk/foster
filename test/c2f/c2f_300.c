#include <stdio.h>

struct T {
  int a;
  int b;
};

int main() {
  struct T w = { 1, 2 };
  printf("%d\n", w.a);
  printf("%d\n", w.b);
  struct T x = { 0 };
  printf("%d\n", x.a);
  printf("%d\n", x.b);
  struct T y = { .a = 4 };
  printf("%d\n", y.a);
  printf("%d\n", y.b);
  struct T z = { .b = 3 };
  printf("%d\n", z.a);
  printf("%d\n", z.b);
  struct T q = { .a = 1, .b = 2 };
  printf("%d\n", q.a);
  printf("%d\n", q.b);
  return 0;
}
