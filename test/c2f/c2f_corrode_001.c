int sum(int count)
{
  goto a;

b:
  --count;
  goto d;

a: ;
  int x = 0;
  goto d;

c:
  return x;

d:
  if(count <= 0)
    goto c;
  goto e;

e:
  x += count;
  goto b;
}

#include <stdio.h>
int main() {
  printf("%d\n", sum(-1));
  printf("%d\n", sum(0));
  printf("%d\n", sum(1));
  printf("%d\n", sum(2));
  printf("%d\n", sum(3));
  return 0;
}
