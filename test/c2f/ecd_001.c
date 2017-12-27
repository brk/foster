#include <stdio.h>

struct msg {
  enum { NONE=0, FIELD, VALUE } last;
};

int main() {
  struct msg m; m.last = FIELD;
  printf("%d\n", (int) m.last);
  return 0;
}
