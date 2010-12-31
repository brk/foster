// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/lock.h"

#include "libfoster.h"
#include "libfoster_gc_roots.h"

using namespace foster::runtime;

Lock coro_create_mutex;

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

// coro_transfer may be defined as a macro or assembly-
// language "function." The purpose of foster_coro_transfer
// is to get a symbol with regular C linkage.
void foster_coro_transfer(coro_context* prev, coro_context* next) {
  coro_transfer(prev, next);
}

void foster_coro_destroy(coro_context* ctx) {
  (void) coro_destroy(ctx);
}

struct foster_coro_i32_i32 {
  foster_generic_coro g;
  int32_t arg;
};

void foster_coro_wrapper_i32_i32(void* f_c) {
  foster_coro_i32_i32* fc = (foster_coro_i32_i32*) f_c;
  typedef int32_t(*fn_i32_i32)(void*, int32_t);
  fn_i32_i32 f = (fn_i32_i32) fc->g.fn;

  foster_coro_i32_i32* sibling
    = (foster_coro_i32_i32*) fc->g.sibling;
  sibling->arg = f(fc->g.env, fc->arg);

  fc->g.status = FOSTER_CORO_DEAD;
  foster_assert(false, "unexpectedly reached the end of a coroutine!");
  // hmm, want to clean up, which means ensuring that control flow
  // for the original thread returns to main(). what can we assume
  // is not corrupted?
}

// Transfer control from current coroutine to target coro,
// and mark target as being the current coroutine while remembering the prev.
int32_t coro_invoke_i32_i32(foster_coro_i32_i32* coro, int32_t arg) {
   foster_generic_coro* acoro = &coro->g;
   fprintf(stdout, "coro @%p\n", coro);
   fprintf(stdout, "    fn=%p, status=%d, sibling->status=%d\n",
     acoro->fn, acoro->status, acoro->sibling->status);
   bool is_yielding = acoro->fn == NULL;
   if (is_yielding) {
     foster_assert(acoro->status = FOSTER_CORO_SUSPENDED,
                 "can only yield to a suspended coroutine");
   } else {
     foster_assert(acoro->status = FOSTER_CORO_DORMANT,
                 "can only resume a dormant coroutine");
   }

   coro->arg = arg;
   // TODO once we have multiple threads, this will need to
   // be done atomically (and error handling added).
   acoro->status = is_yielding ? FOSTER_CORO_INVALID
                               : FOSTER_CORO_RUNNING;
   acoro->sibling->status = (is_yielding) ? FOSTER_CORO_DORMANT
                                          : FOSTER_CORO_SUSPENDED;

   // If there's no fn, it must mean we're yielding rather than invoking,
   // and we'll pop the stack when we reappear on the other side of the
   // call to foster_coro_transfer.
   if (!is_yielding) { // push gcoro on the coro "stack"
     acoro->invoker = (foster_generic_coro*) current_coro;
     current_coro = acoro;
   }
   foster_coro_transfer(&acoro->sibling->ctx, &acoro->ctx);
   // Returning from a invoke means we're acting as a yield now,
   // and vice-versa. Yes, this means that, until the end of the
   // function, "!is_yielding" means we're acting as a yield...
   if (!is_yielding) { // likewise, pop the "stack"
     current_coro = (foster_generic_coro*) current_coro->invoker;
   }
   // So if we were originally yielding, then we are
   // now being re-invoked, possibly by a different
   // coro and/or a different thread!
   // But our sibling coro remains the same, it's just the
   // stack that it refers to that might have changed.
   acoro->status = (is_yielding) ? FOSTER_CORO_SUSPENDED
                                 : FOSTER_CORO_DORMANT;
   acoro->sibling->status = (is_yielding) ? FOSTER_CORO_RUNNING
                                          : FOSTER_CORO_INVALID;
   foster_coro_i32_i32* sibling =
       (foster_coro_i32_i32*) acoro->sibling;
   return sibling->arg;
}

// Transfer control from currently executing coroutine to its sibling,
// and mark the previous as being the new current.
int32_t coro_yield_i32_i32(int32_t arg) {
  foster_assert(current_coro != NULL, "cannot yield before invoking a coroutine!");

  // The sibling we yield to should be suspended
  return coro_invoke_i32_i32((foster_coro_i32_i32*) current_coro->sibling, arg);
}

foster_coro_i32_i32*
coro_create_i32_i32(FosterClosurei32i32* pclo) {
  foster_coro_i32_i32* fcoro = (foster_coro_i32_i32*) memalloc(sizeof(foster_coro_i32_i32));
  foster_coro_i32_i32* ccoro = (foster_coro_i32_i32*) memalloc(sizeof(foster_coro_i32_i32));
  foster_coro_create(foster_coro_wrapper_i32_i32, fcoro);

  // We don't fill in the sibling context pointer yet because
  // we don't know that the coro will be invoked by this thread...
  fcoro->g.sibling = reinterpret_cast<foster_generic_coro*>(ccoro);
  ccoro->g.sibling = reinterpret_cast<foster_generic_coro*>(fcoro);
  fcoro->g.fn = reinterpret_cast<coro_func>(pclo->code);
  fcoro->g.env = pclo->env;
  ccoro->g.fn  = NULL;
  ccoro->g.env = NULL;
  fcoro->g.invoker = NULL;
  ccoro->g.invoker = NULL;
  fcoro->g.status = FOSTER_CORO_DORMANT;
  ccoro->g.status = FOSTER_CORO_INVALID;

  fcoro->arg = 555;
  ccoro->arg = 666;
  return (foster_coro_i32_i32*) fcoro;
}

} // extern "C"

