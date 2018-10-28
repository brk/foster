#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

// gcc -std=c99 -O2 csiphash_driver.c
// ./a.out <srclen> <rounds>
//
// if rounds is even, the result printed will be 0;
// if rounds is odd , the actual results will be shown.

uint64_t siphash24(const void *src, unsigned long src_sz, const char key[16]);

int main(int argc, char** argv) {
  int srclen = 1;
  int rounds = 10000;
  int i, round;

  if (argc >= 1) { srclen = atoi(argv[1]); }
  if (argc >= 2) { rounds = atoi(argv[2]); }

  char* bytes = (char*) malloc(srclen + 1);
  for (i = 0; i < srclen; ++i) { bytes[i] = (char) (i % 255); }

  const char key[16] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14 ,15 };

  uint64_t res = 0;
  for (round = 0; round < rounds; ++round) {
    res = res ^ siphash24((const void*) bytes, srclen, key);
  }

  printf("%" PRIx64 "\n", res);

  free(bytes);

  return 0;
}

