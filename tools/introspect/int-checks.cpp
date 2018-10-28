// Copyright (c) 2016 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <iostream>
#include <sstream>
#include "cycle.h"
#include <cstdlib>
#include <random>
#include <type_traits>

using namespace std;

template<typename T>
T genRand() {

}

template<typename T>
std::vector<T> genOne(int tagged_per_1000, bool tagHigh) {
  T rv = 0;
}

template<typename T>
std::vector<T> gen(int size, int tagged_per_1000, T tagMask) {
  std::random_device r;

  std::default_random_engine e1(r());
  std::uniform_int_distribution<T> raw(0, 1<<20);
  std::uniform_int_distribution<T> dotag_dist(0, 1000);
  int pretagged = 0;
  std::vector<T> rv(size);
  for (int i = 0; i < size; ++i) {
    rv[i] = raw(e1) & (~tagMask);
    if (dotag_dist(e1) < tagged_per_1000) {
      rv[i] = rv[i] | tagMask;
    }
  }
  return rv;
}

template<typename T>
T examine_vec_bare(const std::vector<T>& vec, int& tagged) {
  T prev      = 0;
  T acc       = 0;
  for(auto it = vec.begin(); it != vec.end(); ++it) {
    T val       = *it;
    T next      = val + prev;
    acc        += next;
    prev        = val;
  }
  return acc;
}

extern "C" int slowpath(void);

template<typename T>
T examine_vec_highbit(const std::vector<T>& vec, int& tagged) {
  typedef typename std::make_signed<T>::type TS;
  T prev      = 0; // Assumed/unchecked invariant: prev stays in non-ptr repr.
  T acc       = 0;
  for(auto it = vec.begin(); it != vec.end(); ++it) {
    T val       = *it;
    // Overflow means bit 63/64 becomes set, which we detect
    // by shifting into the sign bit and comparing with zero.
    if (TS(val << T(1)) < 0) {
      acc += T(slowpath());
      ++tagged;
    } else {
      T next    = val + prev;
      acc       += TS(next); // if no overflow, value is in low bits as usual.
    }
    prev        = val;
  }
  return acc;
}

template<typename T>
T examine_vec_lowbit(const std::vector<T>& vec, int& tagged) {
  T prev      = 0;
  T acc       = 0;
  for(auto it = vec.begin(); it != vec.end(); ++it) {
    T val       = *it;
    // Low bit tagged means int; untagged means pointer.
    if (val & 1) {
      T next    = val + prev;
      acc       += next >> 1;
    } else {
      acc += T(slowpath());
      ++tagged;
    }
    prev        = val;
  }
  return acc;
}

template<typename T>
void bench_hmm(int size, int iters, int tagged_per_1000, T tagMask, T (*func)(const std::vector<T>&, int&)) {
  auto vec = gen<T>(size, tagged_per_1000, tagMask);
  uint64_t acc = 0;
  int tagged = 0;

  ticks bt   = getticks();
  for (int i = 0; i < iters; ++i) {
    tagged   = 0;
    acc += func(vec, tagged);
  }
  ticks et = getticks();

  //printf("  ticks: %f\n", elapsed(et, bt));
  printf("  ticks/elt: %f    (tagged = %d)\n", elapsed(et, bt) / (double(size) * double(iters)), tagged);
  //printf("  %d iters * %d elts = %lld ops\n", iters, size, int64_t(iters) * int64_t(size));

  if (acc == 0) { printf("!\n"); }
}

void bench(int iters, int tagged_per_1000, std::string name) {
  uint64_t highMask = 1ULL << 62;
  uint64_t lowMask = 1ULL;
  if (name == "highbit_64_1e2") { bench_hmm(1e2, iters, tagged_per_1000, highMask, examine_vec_highbit); }
  if (name == "highbit_64_1e5") { bench_hmm(1e5, iters, tagged_per_1000, highMask, examine_vec_highbit); }

  if (name == "lowbit_64_1e2") { bench_hmm(1e2, iters, tagged_per_1000, lowMask, examine_vec_lowbit); }
  if (name == "lowbit_64_1e5") { bench_hmm(1e5, iters, tagged_per_1000, lowMask, examine_vec_lowbit); }

  if (name == "bare_64_1e5") { bench_hmm(1e5, iters, tagged_per_1000, lowMask, examine_vec_bare); }

  uint32_t highMask32 = 1 << 30;
  uint32_t lowMask32 = 1;
  if (name == "highbit_32_1e2") { bench_hmm(1e2, iters, tagged_per_1000, highMask32, examine_vec_highbit); }
  if (name == "highbit_32_1e5") { bench_hmm(1e5, iters, tagged_per_1000, highMask32, examine_vec_highbit); }

  if (name == "lowbit_32_1e2") { bench_hmm(1e2, iters, tagged_per_1000, lowMask32, examine_vec_lowbit); }
  if (name == "lowbit_32_1e5") { bench_hmm(1e5, iters, tagged_per_1000, lowMask32, examine_vec_lowbit); }

  if (name == "bare_32_1e5") { bench_hmm(1e5, iters, tagged_per_1000, lowMask32, examine_vec_bare); }
}

int main(int argc, char** argv) {
  if (argc < 4) {
    cerr << "Usage: int-checks <iterations> <tagged_per_1000> testname" << endl;
    cerr << "Test names:" << endl;
    cerr << "             highbit_64_1e2" << endl;
    cerr << "             highbit_64_1e5" << endl;
    return 1;
  }

  int iterations = 0;
  { string s = argv[1];
    stringstream ss(s); ss >> iterations; }

  int tagged_per_1000 = 0;
  { string s = argv[2];
    stringstream ss(s); ss >> tagged_per_1000; }

  bench(iterations, tagged_per_1000, string(argv[3]));

  return 0;
}

