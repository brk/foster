// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/lock.h"

#include "libfoster.h"
#include "libfoster_gc_roots.h"
#include "foster_gc.h"

using namespace foster::runtime;

#define TRACE do { fprintf(stdout, "%s::%d\n", __FILE__, __LINE__); fflush(stdout); } while (0)

Lock coro_create_mutex;

namespace foster {
namespace runtime {

  const char* coro_status(int status) {
    switch (status) {
    case FOSTER_CORO_INVALID: return "invalid";
    case FOSTER_CORO_SUSPENDED: return "suspended";
    case FOSTER_CORO_DORMANT: return "dormant";
    case FOSTER_CORO_RUNNING: return "running";
    case FOSTER_CORO_DEAD: return "dead";
    default: return "unknown";
    }
  }

  void coro_print(foster_generic_coro* coro) {
    if (!coro) return;
    printf("coro %p: ", coro); fflush(stdout);
    printf("sibling %p, invoker %p, status %s, fn %p\n",
        coro->sibling, coro->invoker, coro_status(coro->status), coro->fn);
  }

  void coro_dump(foster_generic_coro* coro) {
    if (!coro) {
      printf("cannot dump NULL coro ptr!\n");
    } else if (0) {
      foster::runtime::coro_print(coro);
      foster::runtime::coro_print(coro->sibling);
    }
  }

  // coro_transfer may be defined as a macro or assembly-
  // language "function." The purpose of foster_coro_transfer
  // is to get a symbol with regular C linkage, and to ensure
  // that the coro_transfer function appears in the LLVM module.
  void
  foster_coro_transfer(foster_generic_coro* coro) {
    coro_transfer(&coro->sibling->ctx, &coro->ctx);
  }

}
} // namespace foster::runtime

////////////////////////////////////////////////////////////////////

extern "C" {

// corofn :: void* -> void
void foster_coro_create(coro_func corofn,
                        void* arg) {
  AutoLock locker(coro_create_mutex);

  long ssize = 16*1024;
  // TODO allocate small stacks that grow on demand
  // (via reallocation or stack segment chaining).
  // TODO use mark-sweep GC for coro stacks.
  void* sptr = malloc(ssize);
  foster_generic_coro* coro = (foster_generic_coro*) arg;
  coro_create(&coro->ctx, corofn, coro, sptr, ssize);
}

// This is a no-op for the CORO_ASM backend,
// but we should still call it anyways (TODO).
void foster_coro_destroy(coro_context* ctx) {
  (void) coro_destroy(ctx);
}

} // extern "C"

