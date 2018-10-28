#include <stdio.h>

enum sillies {
  foo = 2
};

void f(int x) {
  switch(x) {
  case (foo << 10 | 12 | ' '):
    printf("%d\n", 11);
    break;
  default:
    printf("%d\n", 0);
  }
}

int main() {
  f(foo << 10 | 12 | ' ');
  f(42);
  return 0;
}
