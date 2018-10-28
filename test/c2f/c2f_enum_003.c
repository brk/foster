#include <stdio.h>

enum sillies {
  foo = 2
, bar
};

void f(int x) {
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
  f(42);
  return 0;
}
