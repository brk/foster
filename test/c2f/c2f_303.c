#include <stdio.h>

typedef struct {
  int z; int q;
} foo;

int main() {
  foo v = { 4, 5 };
  printf("%d\n", v.z + v.q);
  return 0;
}
