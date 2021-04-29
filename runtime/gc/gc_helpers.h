// Copyright (c) 2021 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GC_HELPERS
#define FOSTER_GC_HELPERS

#include <cinttypes> // for intptr_t and uintptr_t
#include <cstddef> // for size_t

// E.g. if powerOf2 is 4, performs the following mapping:
// 0 -> 0      1 -> 4
// 2 -> 4      3 -> 4
// 4 -> 4      5 -> 8
template <typename T>
inline T roundUpToNearestMultipleWeak(T v, uintptr_t powerOf2) {
  uintptr_t mask = powerOf2 - 1;
  return T((uintptr_t(v) + mask) & ~mask);
}

// Performs byte-wise addition on void pointer base
inline void* offset(void* base, intptr_t off) {
  return (void*) (((char*) base) + off);
}

template<typename T>
inline void incr_by(T* & base, intptr_t off) {
  base = (T*) offset((void*)base, off);
}

inline size_t distance(void* base, void* bound) {
  return (char*) bound - (char*) base;
}

inline bool low_bits_zero(uintptr_t val, uintptr_t n) {
  return val == ((val >> n) << n);
}


#endif // FOSTER_GC_HELPERS