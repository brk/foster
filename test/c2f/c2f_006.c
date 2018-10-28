#include <stdio.h>

void direct() {
  int z = 0; int o = 1; int t = 2; int r = 3;
  printf("%d\n", (z || z));
  printf("%d\n", (z || o));
  printf("%d\n", (o || z));
  printf("%d\n", (o || t));
  printf("%d\n", (t || r));
  int x = 3;
  if (z || z) { x = x + 1; }
  //if (z || o) { x = x + 10; }
  x = (z || o) ? x + 10 : x;
  printf("%d\n", x);
}

int viacfg() {
  int z = 0; int o = 1; int t = 2; int r = 3;
  if (z) return 11;
  printf("%d\n", (z || z));
  printf("%d\n", (z || o));
  printf("%d\n", (o || z));
  printf("%d\n", (o || t));
  printf("%d\n", (t || r));
  int x = 3;
  if (z || z) { x = x + 1; }
  if (z || o) { x = x + 10; }
  printf("%d\n", x);
  return 22;
}

void viacfg_void() {
  int z = 0;
  if (z) return;
  z = 3;
  return;
}

int main() {
  direct();
  printf("%d\n", viacfg());
  viacfg_void();
  return 0;
}

