#include <stdint.h>
#include <stdio.h>

int32_t do_something_eh(int32_t x, int32_t y);
void    loopy_but_not_allocating(int32_t x, int32_t y);

void frozzle(int32_t x) {
  printf("%d\n", x);
}

int main() {
  printf("%d\n", do_something_eh(2, 3));
  loopy_but_not_allocating(1, 2);
  return 0;
}
