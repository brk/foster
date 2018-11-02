#include <stdlib.h>
#include <stdio.h>

typedef struct {
  int x;
} foo;

int main() {
 foo* f = malloc(sizeof(foo));
 f->x = 42;
 printf("%d\n", f->x);
 return 0;
}
