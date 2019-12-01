#include <stdio.h>

int __ac_X31_hash_string(const char *s)
{
	int h = (int)*s;
	if (h) for (++s ; *s; ++s) h = (h << 5) - h + (int)*s;
	return h;
}

void ptr_incr_value(int* s) {
  int* c;
  c = ++s;
  printf("%d\n", *c);
}
void ptr_incr_unit(int* s) {
  int* c, d;
  ++s;
  d = *(c = ++s);
  printf("%d\n", *s);
  printf("%d\n", *c);
  printf("%d\n", d);
}

int main() {
  int arr[] = { 2, 3, 4 };
  printf("%d\n", __ac_X31_hash_string("foobar! "));

  ptr_incr_value(arr);
  ptr_incr_unit(arr);

  return 0;
}
