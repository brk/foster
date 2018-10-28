#include <stdio.h>

typedef struct {
  int z;
} T;

int main() {
  T v = { 4 };
  printf("%d\n", v.z);
  return 0;
}
