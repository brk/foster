#include <stdio.h>

typedef struct {
  int z; int q;
} T;

int main() {
  T v = { 4, 5 };
  printf("%d\n", v.z + v.q);
  return 0;
}
