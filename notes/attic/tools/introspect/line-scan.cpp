// Copyright (c) 2016 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <iostream>
#include <sstream>
#include "cycle.h"
#include <cstdlib>
#include <random>
#include <type_traits>
#include <cstring>

using namespace std;

uint64_t do_scan_8(uint8_t* vec, int size, int i) {
  for (int i = 0; i < size; ++i) {
    if (vec[i] != 0) return i;
  }
  return 0;
}

uint64_t do_scan_64(uint8_t* vec, int size, int i) {
  uint64_t* v64 = (uint64_t*) vec;
  int size64 = size / 8;
  for (int i = 0; i < size64; ++i) {
    if (vec[i] != 0) return i;
  }
  return 0;
}

void bench_scan64(int size, int iters) {
  uint8_t* vec = (uint8_t*)malloc(size);
  memset(vec, 0, size);

  uint64_t acc = 0;

  ticks bt   = getticks();
  for (int i = 0; i < iters; ++i) {
    acc += do_scan_64(vec, size, i);
  }
  ticks et = getticks();

  printf(" size %d, @64 ticks: %f\n", size, elapsed(et, bt));
  printf(" size %d, @64 ticks/elt: %f\n", size, elapsed(et, bt) / (double(size) * double(iters)));
  if (acc == 0) { printf("!\n"); }
}
void bench_scan8(int size, int iters) {
  uint8_t* vec = (uint8_t*)malloc(size);
  memset(vec, 0, size);

  uint64_t acc = 0;

  ticks bt   = getticks();
  for (int i = 0; i < iters; ++i) {
    acc += do_scan_8(vec, size, i);
  }
  ticks et = getticks();

  printf(" size %d, @8 ticks: %f\n", size, elapsed(et, bt));
  printf(" size %d, @8 ticks/elt: %f\n", size, elapsed(et, bt) / (double(size) * double(iters)));
  if (acc == 0) { printf("!\n"); }
}

int main(int argc, char** argv) {
  bench_scan8(8192, 1);
  bench_scan64(8192, 1);
  return 0;
}

