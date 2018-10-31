#include <stdio.h>
#include <stdlib.h>
typedef struct {
  int e;
} entry;

typedef struct {
  entry* entries;
  entry* single;
} foo;

int main() {
  /*
  foo fv;
  foo* f = & fv;
  */
  foo* f = (foo*) malloc(sizeof(foo));
  f->entries = (entry*) malloc(sizeof(entry) * 100);
  f->single = (entry*) malloc(sizeof(entry));
  f->single->e = 44;
  f->entries[0].e = 42;
  f->entries[1].e = 43;
  entry* en1 = &f->entries[1];
  entry* en2;
  en2 = f->entries++;
  entry* en3;
  en3 = f->entries;
  entry* sing;
  sing = f->single;
  printf("%d\n", en2->e);
  printf("%d\n", en3->e);
  printf("%d\n", sing->e);
  return 0;
}
