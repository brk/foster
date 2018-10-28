#include <stdio.h>
int main() {
  int a = 0;
  ++a;
  (void)(0);
  --a;
  printf("%d\n", a);
  return a;
}
