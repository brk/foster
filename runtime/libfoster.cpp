#include <cstdio>

int fprint_i32(FILE* f, int x) { return fprintf(f, "%d\n", x) - 1; }
int fprint_i32x(FILE* f, int x) { return fprintf(f, "%X_16\n", x) - 1; }
int fprint_i32b(FILE* f, int x) {
  static char buf[33];
  buf[32] = '\0';
  for (int i = 0; i < 32; ++i) {
    buf[31 - i] = (x & (1<<i)) ? '1' : '0';
  }
  return fprintf(f, "%s_2\n", buf);
}

extern "C" {
int print_i32(int x) { return fprint_i32(stdout, x); }
int expect_i32(int x) { return fprint_i32(stderr, x); }

int print_i32x(int x) { return fprint_i32x(stdout, x); }
int expect_i32x(int x) { return fprint_i32x(stderr, x); }

int print_i32b(int x) { return fprint_i32b(stdout, x); }
int expect_i32b(int x) { return fprint_i32b(stderr, x); }
} // extern "C"



