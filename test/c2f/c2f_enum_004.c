#include <stdio.h>

typedef enum {
  foo = 2
, bar
} sillies;

void f(sillies x) {
  switch(x) {
  case foo:
    printf("%d\n", 11);
    break;
  case bar:
    printf("%d\n", 22);
    break;
  default:
    printf("%d\n", 0);
  }
}

int main() {
  f(foo);
  f(bar);
  f(bar - 1);
  f(42);
  return 0;
}
