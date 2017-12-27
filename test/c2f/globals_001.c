#include <stdio.h>

int foo = 3;
const char* blah[] = { "meh", "hum", NULL };
int main() {
  printf("%d\n", foo);
  printf("%s\n", blah[0]);
  printf("%s\n", blah[1]);
  return 1;
}
