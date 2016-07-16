// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "libfoster.h"
#include "libfoster_gc_roots.h"
#include "foster_gc.h"

#include <cstring> // for memset

using namespace foster::runtime;

#define TRACE do { fprintf(stdout, "%s::%d\n", __FILE__, __LINE__); fflush(stdout); } while (0)

namespace foster {
namespace runtime {

  int32_t              coro_status(foster_generic_coro* c) { return c->status; }
  foster_generic_coro* coro_sibling(foster_generic_coro* c) { return c->sibling; }
  foster_generic_coro* coro_invoker(foster_generic_coro* c) { return c->invoker; }
  CoroProc             coro_fn(foster_generic_coro* c) { return c->fn; }
  coro_context         coro_ctx(foster_generic_coro* c) { return c->ctx; }

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
  long ssize = 8*1024*sizeof(void*);
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

