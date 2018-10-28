#include <stdio.h>

typedef struct P_t {
  int x;
  int y;
} P;

int main(void) {
  P a = { 1, 2 };
  P b = { .x = 2, .y = 1 };

  printf("%d\n", a.x);
  printf("%d\n", a.y);
  printf("%d\n", b.x);
  printf("%d\n", b.y);
  return 0;
}
