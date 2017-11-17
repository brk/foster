#include <stdio.h>

int main(void) {
  {
    int x = 4;

    printf("%d\n", x);
    goto bar;

    bar2:;
    x = 32;
    printf("%d\n", x);
    goto bar3;

    bar4:;
    x = -3;
    printf("%d\n", x);
  }
  return 0;

  {
    int x = 55;

    bar:;
    x = 44;
    printf("%d\n", x);
    goto bar2;

    bar3:;
    x = 66;
    printf("%d\n", x);
    goto bar4;
  }
}
