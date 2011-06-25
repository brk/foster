// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef LIBFOSTER_GC_ROOTS_H
#define LIBFOSTER_GC_ROOTS_H

#include <cstdio>
#include <cstdlib>
#include <inttypes.h>
#include "libcoro/coro.h"

struct foster_generic_coro {
  coro_context ctx;
  foster_generic_coro* sibling;
  void (*fn)(void*);
  void* env;
  foster_generic_coro* invoker;
  foster_generic_coro** indirect_self;
  int32_t status;
};

// Thanks to its single-threaded semantics, Lua gets by without
// needing to distinguish between suspended and dormant coroutines.
enum {
  FOSTER_CORO_INVALID,
  /// coro which has been invoked from but not yet yielded back to.
  /// Not safe for another thread to steal!
  FOSTER_CORO_SUSPENDED,
  /// coro which has no subcoroutines: no action yet, or last
  /// action was a yield.
  FOSTER_CORO_DORMANT,
  FOSTER_CORO_RUNNING,
  FOSTER_CORO_DEAD
};

// (eventually, per-thread variable)
// coro_invoke(c) sets this to c.
// coro_yield() resets this to current_coro->invoker.
extern "C" foster_generic_coro* current_coro;

namespace foster {
namespace runtime {

// We can't rely on assert() to print messages for us when we're
// not on the main thread's stack.
inline void foster_assert(bool ok, const char* msg) {
  if (!ok) {
    fprintf(stderr, "%s\n", msg);
    fflush(stderr);
    exit(1);
  }
}

} // namespace foster::runtime
} // namespace foster

#endif
