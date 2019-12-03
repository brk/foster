#include <stdio.h>
int part1() {
  int array[1]; array[0] = 42; return array[0];
}
int part2() {
  int array[2] = { 10, 0 }; array[1] = 100; return array[0] + array[1];
}

int glub[2] = { 1, 2 };

int main() {
  printf("%d\n", part1());
  printf("%d\n", part2());
  return 0;
}
