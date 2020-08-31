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

  int32_t              coro_status(foster_bare_coro* c) { return c->status; }
  foster_bare_coro*    coro_parent(foster_bare_coro* c) { return c->parent; }
  CoroProc             coro_fn(foster_bare_coro* c) { return c->fn; }
  coro_context         coro_ctx(foster_bare_coro* c) { return c->ctx; }

  // coro_transfer may be defined as a macro or assembly-
  // language "function." The purpose of foster_coro_transfer
  // is to get a symbol with regular C linkage, and to ensure
  // that the coro_transfer function appears in the LLVM module.
  void
  foster_force_linking_of_coro_transfer(foster_bare_coro* coro) {
    coro_transfer(&coro->ctx, &coro->ctx);
  }

}
} // namespace foster::runtime

////////////////////////////////////////////////////////////////////

extern "C" {

foster_bare_coro** __foster_get_current_coro_slot();
foster_bare_coro* foster_get_current_coro_parent() {
  return foster::runtime::coro_parent(*__foster_get_current_coro_slot());
}

foster_bare_coro* foster__lookup_handler_for_effect(int64_t tag) {
  //printf("  Current coro tag: %lld\n", (*__foster_get_current_coro_slot())->effect_tag);
  foster_bare_coro* c = foster_get_current_coro_parent();
  while (c) {
    //printf("   parent coro tag: %lld\n", c->effect_tag);
    if (c->effect_tag == tag) return c;
    c = coro_parent(c);
  }

  printf("WARNING: foster__lookup_handler_for_effect(%" PRId64 ") couldn't find a matching coro!\n", tag);
  return NULL;
}

void foster_coro_ensure_self_reference(foster_bare_coro* coro) {
  if (coro->indirect_self != NULL) {
    *(coro->indirect_self) = coro;
  }
}

bool foster_coro_isdead(foster_bare_coro* coro) {
  return foster::runtime::coro_status(coro) == FOSTER_CORO_DEAD;
}

// corofn :: void* -> void
void foster_coro_create(coro_func corofn, void* arg) {
   // 100 MB stacks just in case; but note it's virtual addr space only
  long ssize = 100*1024*1024*sizeof(void*);

  // TODO allocate small stacks that grow on demand
  // (via reallocation or stack segment chaining).
  // TODO use mark-sweep GC for coro stacks.

  coro_stack sinfo;
  if (!coro_stack_alloc(&sinfo, ssize / sizeof(void*))) {
    // If we don't format the ssize argument here, the compiler
    // will translate the fprintf to a call to fwrite.
    // Due to the way the backend imports this code, the result can
    // be that fwrite is given a type that doesn't unify with other
    // foreign-import-ed libc functions, or functions like c2f_stdout.
    // Forcing usage of fprintf is preferable because c2f.foster
    // doesn't import it by default.
    fprintf(stderr, "Coro stack allocation of size %ld failed!\n", ssize);
    fflush(stderr);
    exit(2);
  }
  //fprintf(stderr, "allocating a coro stack of size %ld (0x%lx): %p\n", ssize, ssize, sinfo.sptr);
  //memset(sinfo.sptr, 0xEE, ssize); // for debugging only
  foster_bare_coro* coro = (foster_bare_coro*) arg;
  coro->indirect_self = (foster_bare_coro**) malloc(sizeof(coro));
  foster_coro_ensure_self_reference(coro);
  libcoro__coro_create(&coro->ctx, corofn, coro->indirect_self,
                       sinfo.sptr, sinfo.ssze);
}

// This is a no-op for the CORO_ASM backend,
// but we should still call it anyways (TODO).
void foster_coro_destroy(coro_context* ctx) {
  // We need to call this function from this module, somewhere,
  // to force LLVM to include a declaration in this bitcode
  // module, which then ensures that the generic coro struct type
  // isn't duplicated when we link the modules together
  // after manually adding a declaration in fosterlower.
  (void)__foster_get_current_coro_slot();

  (void) coro_destroy(ctx);
}

void foster_coro_delete_self_reference(void* vc) {
  foster_bare_coro* coro = (foster_bare_coro*) vc;
  free(coro->indirect_self);
  coro->indirect_self = NULL;
}

} // extern "C"

