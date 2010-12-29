// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef LIBFOSTER_GC_ROOTS_H
#define LIBFOSTER_GC_ROOTS_H

#include <inttypes.h>

struct foster_generic_coro_i32_i32 {
  void* pctx;
  void* sibling;
  void (*fn)(void*);
  void* env;
  void* invoker;
  int32_t status;
  int32_t arg;
};


// Thanks to its single-threaded semantics,
// Lua gets by without needing to distinguish between
// suspended+active and suspended+inactive coroutines.
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
extern foster_generic_coro_i32_i32* current_coro;

namespace foster {
namespace runtime {

} // namespace foster::runtime
} // namespace foster

#endif
