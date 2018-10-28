#include <stdio.h>
#include <string.h>
#include <stdint.h>

int main() {
  char foo[8];
  printf("%d\n", (int)(sizeof foo));

  printf("%d\n", memcmp(foo, foo, sizeof foo));
  printf("%d\n", (memcmp(foo, foo, sizeof foo) ? 23 : 42));
    return 0;
}
