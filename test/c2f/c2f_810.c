#include <stdio.h>

int main() {
  int a = 0;
  int b = ++a;
  int c = a++;
  printf("%d\n", a);
  printf("%d\n", b);
  printf("%d\n", c);

  const char* s = "foobar";
  printf("%s\n", s);
  const char* p = ++s;
  char q = *(s++);
  printf("%s\n", s);
  printf("%s\n", p);
  printf("%d\n", (int)q);
  return 0;
}
