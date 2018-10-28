// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef LIBFOSTER_GC_ROOTS_H
#define LIBFOSTER_GC_ROOTS_H

#include <cstdio>
#include <cstdlib>
#include <inttypes.h>
#include "libcoro/coro.h"

typedef void (*CoroProc)(void*);

// Keep synchronized with foster_generic_coro_ast defined in fosterlower.cpp
// and the offsets in Codegen-coro.cpp
struct foster_bare_coro {
  coro_context ctx;
  CoroProc fn;
  void* env;
  foster_bare_coro* parent;
  foster_bare_coro** indirect_self;
  int64_t effect_tag;
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

namespace foster {
namespace runtime {

  int32_t              coro_status(foster_bare_coro* c);
  foster_bare_coro*    coro_parent(foster_bare_coro* c);
  CoroProc             coro_fn(foster_bare_coro* c)    ;
  coro_context         coro_ctx(foster_bare_coro* c)   ;

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
