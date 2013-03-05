// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster.h"
#include "libfoster_gc_roots.h"
#include "foster_gc.h"

#include <cstring> // for memset

#ifdef FOSTER_MULTITHREADED
#include "base/synchronization/lock.h"
base::Lock g_coro_create_mutex;
#endif

using namespace foster::runtime;

#define TRACE do { fprintf(stdout, "%s::%d\n", __FILE__, __LINE__); fflush(stdout); } while (0)

// (eventually, per-thread variable)
// coro_invoke(c) sets this to c.
// coro_yield() resets this to current_coro->invoker.
foster_generic_coro* current_coro;

namespace foster {
namespace runtime {

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

void foster_coro_ensure_self_reference(foster_generic_coro* coro) {
  if (coro->indirect_self != NULL) {
    *(coro->indirect_self) = coro;
  }
}

// corofn :: void* -> void
void foster_coro_create(coro_func corofn,
                        void* arg) {
#ifdef FOSTER_MULTITHREADED
  base::AutoLock locker(g_coro_create_mutex);
#endif

  long ssize = 16*1024;
  // TODO allocate small stacks that grow on demand
  // (via reallocation or stack segment chaining).
  // TODO use mark-sweep GC for coro stacks.
  void* sptr = malloc(ssize);
  memset(sptr, 0xEE, ssize); // for debugging only
  foster_generic_coro* coro = (foster_generic_coro*) arg;
  coro->indirect_self = (foster_generic_coro**) malloc(sizeof(coro));
  foster_coro_ensure_self_reference(coro);
  coro_create(&coro->ctx, corofn, coro->indirect_self,
              sptr, ssize);
}

// This is a no-op for the CORO_ASM backend,
// but we should still call it anyways (TODO).
void foster_coro_destroy(coro_context* ctx) {
  (void) coro_destroy(ctx);
}

void foster_coro_delete_self_reference(void* vc) {
  foster_generic_coro* coro = (foster_generic_coro*) vc;
  free(coro->indirect_self);
  coro->indirect_self = NULL;
}

} // extern "C"

