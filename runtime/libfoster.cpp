// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <cstdio>
#include <inttypes.h>
#include <cstdlib>
#include <vector>

#include <pthread.h>

#include "imath.h"
#include "foster_gc.h"
#include "cpuid.h"
#include "libcoro/coro.h"

// This file provides the bootstrap "standard library" of utility functions for
// programs compiled (to LLVM IR) with foster. Making these functions available
// to compiled programs is a semi-automated process that could still be
// improved. Current steps for adding a new library function:
//   1) Write the implementation using whatever C++ features are needed.
//   2) Add a wrapper function in the `extern "C"` section below.
//
// TODO: hybrid foster/C++ library functions
//
// The build system must take extra steps to link foster-compiled LLVM IR to
// this code, but those steps are independent of adding new functions.
// Specifically, we must assemble the IR to bitcode (with llvm-as),
// compile this file to bitcode (with llvm-gcc or clang),
// and link the two bitcode files together.
//
// These steps are, as of this writing, done via shell scripts and the code in
// test/bootstrap/run_all.py
//
// Obvious areas for improvement:
//   *) Make foster.cpp figure out how to insert prototypes for standard library
//      functions automatically, rather than manually writing code to insert
//      each prototype separately. In the general case, this probably requires
//      exposing more LLVM IR via Foster. Having the process be completely
//      automated for existing C symbols would be really cool! That would
//      essentially give Foster a "FFI" for interfacing with tons of useful
//      libraries like OpenGL, gmp, and LLVM's C bindings...
//
// Here's a quick sketch:
//   Recognize an expression of the form     import foo
//     and search for foo.ll or foo.bc in the module search path.
// see http://llvm.org/svn/llvm-project/llvm/trunk/tools/llvm-dis/llvm-dis.cpp
//   If found, load the module and (lazily?) extract symbol names.
//   When a lookup for a given name fails in foster.cpp, consult
//   the list of modules to see if it is found. If found, record the extracted
//   type information (and insert the prototype?).
//  (a "complete" solution would also require auto-linking against the module)
//
// This does not deal with block scoping of imports, or of name spaces,
// but it is probably simple enough to be easily implemented, and useful enough
// to make the language much faster to iterate on.

////////////////////////////////////////////////////////////////

std::vector<coro_context> coro_initial_contexts;

struct foster_generic_coro_i32_i32 {
  void* pctx;
  void* sibling;
  void (*fn)(void*);
  void* env;
  int32_t status;
  int32_t arg;
};

// (eventually, per-thread data structure)
// Maintained by coro_invoke_... (which pushes new entries)
// and coro_yield_... (which pops the stack).
std::vector<foster_generic_coro_i32_i32*> current_coro;

namespace foster {
namespace runtime {

void initialize() {
  cpuid_info info;
  cpuid_introspect(info);

  int cachesmall = cpuid_small_cache_size(info);
  int cachelarge = cpuid_large_cache_size(info);

  // TODO Initialize one default coro context per thread.
  coro_initial_contexts.push_back(coro_context());
  coro_create(&coro_initial_contexts[0], 0, 0, 0, 0);

  gc::initialize();
}

void cleanup() {
  gc::cleanup();
}

#ifndef PRId64
#define PRId64 "lld"
#endif

#ifndef PRIX64
#define PRIX64 "llX"
#endif

int fprint_i64(FILE* f, int64_t x) { return fprintf(f, "%" PRId64 "\n", x) - 1; }
int fprint_i64x(FILE* f, int64_t x) { return fprintf(f, "%" PRIX64 "_16\n", x) - 1; }
int fprint_i64b(FILE* f, int64_t x) {
  static char buf[64+1];
  buf[64] = '\0';
  for (int i = 0; i < 64; ++i) {
    buf[63 - i] = (x & (1<<i)) ? '1' : '0';
  }
  return fprintf(f, "%s_2\n", buf);
}

int fprint_i32(FILE* f, int32_t x) { return fprintf(f, "%d\n", x) - 1; }
int fprint_i32x(FILE* f, int32_t x) { return fprintf(f, "%X_16\n", x) - 1; }
int fprint_i32b(FILE* f, int32_t x) {
  static char buf[32+1];
  buf[32] = '\0';
  for (int i = 0; i < 32; ++i) {
    buf[31 - i] = (x & (1<<i)) ? '1' : '0';
  }
  return fprintf(f, "%s_2\n", buf);
}

int fprint_mp_int(FILE* f, mp_int m, int radix) {
  mp_small small;
  mp_result conv = mp_int_to_int(m, &small);
  if (conv != MP_RANGE) {
    switch (radix) {
    case 10: return fprint_i64(f, int64_t(small));
    case 16: return fprint_i64x(f, int64_t(small));
    default: return fprint_i64b(f, int64_t(small));
    }
  }

  mp_result len = mp_int_string_len(m, radix);
  char* buf = (char*) malloc(len);
  mp_result res0 = mp_int_to_string(m, radix, buf, len);
  int rv = fprintf(f, "%s\n", buf);
  free(buf);
  return rv;
}

struct FosterClosurei32i32 {
  int32_t (*code)(void* env, int32_t);
  void* env;
};
//
//std::vector<pthread_t> threadinfo;
//
//void* i32_closure_invoker(void* arg) {
//  FosterClosurei32* c = (FosterClosurei32*) arg;
//  int32_t rv = c->code(c->env);
//  return NULL;
//}

} } // namespace foster::runtime

using namespace foster::runtime;

extern "C" {
  // This interface is slightly awkward, with the extra indirection, because:
  // 1) pthreads wants a function that returns a void*,
  //    which foster doesn't yet do, and
  // 2) llvm-g++ lowers the closure struct type given above, so foster sees
  //    a function of two pointer parameters instead of one struct type param.
  //    (Clang++ lowers to a byval pointer, which is better for us.)
  //    Thus, in order to pass a closure struct to a C function lowered by
  //    llvm-g++, we can:
  //      a) Special-case this function in the typecheck and codegen passes (ew!)
  //      b) Add a generalized automatic-unpacking pass
  //         that applies to all functions (ew!)
  //      c) Track the origin of functions and only automatically unpack structs
  //         if we're calling a C function, and the LLVM types only match with
  //         the unpacking applied. (ugh!)
  //
  // The easiest route would to (implicitly) require that closures
  // be converted to standalone trampolines before being passed in.
  // Unfortunately, trampolines are not universally available on all platforms,
  // for security reasons (they require mutable + executable memory).
  //
  // TODO: The C wrapper may end up being necessary anyways, in order
  // to pass thread id information (as well as the env) back to the callback.
  // Need to decide if and how thread ids and such should be handled.
  //
//int32_t thread_create_i32(FosterClosurei32 c) {
//  int32_t id = threadinfo.size();
//  threadinfo.push_back(pthread_t());
//  return pthread_create(&threadinfo[id], NULL, i32_closure_invoker, (void*) &c);
//}
//
//int32_t thread_waitall() {
//  int nthreads = threadinfo.size();
//  for (int i = 0; i < nthreads; ++i) {
//    pthread_join(threadinfo[i], NULL);
//  }
//  threadinfo.clear();
//  return nthreads;
//}

//int32_t c_invoke_closure_i32(FosterClosurei32 clo) { return clo.code(clo.env); }

// The main complication with supporting a function such as this,
// which allows top-level Foster functions to be passed to C as raw
// function pointers, is that the compiler must duplicate the function
// body and give the duplicate C callconv, instead of fastcc (or whatever).
// Currently, the compiler does not create safely callable duplicates
// for use by C, but we should eventually.
//int32_t c_invoke_fnptr_to_i32(int32_t (*f)()) { return f(); }

//////////////////////////////////////////////////////////////////

// Interface to foster's memory allocator; see gc/foster_gc_allocate.cpp
void* memalloc(int64_t sz);

//////////////////////////////////////////////////////////////////

// coro_func :: void* -> void
coro_context* foster_coro_create(coro_func coro, void *arg) {
  // TODO add a mutex to make this all threadsafe.
  long ssize = 16*1024;
  // TODO allocate small stacks that grow on demand
  // (via reallocation or stack segment chaining).
  // TODO implement garbage collection for coro stacks.
  // We don't allocate coro stacks on the (semispace) GC heap
  // because doing so requires moving the stack pointer
  // after fixing references on the copied stack (but only
  // when running gc from a coroutine...).
  void* sptr = malloc(ssize);
  coro_context* ctx = (coro_context*) memalloc(sizeof(coro_context));
  coro_create(ctx, coro, arg, sptr, ssize);
  return ctx;
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
  coro_context* pctx;
  foster_coro_i32_i32* sibling;
  int32_t (*fn)(void*, int32_t);
  void* env;
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
  FOSTER_CORO_SUSPENDED_ACTIVE,
  /// coro which has no subcoroutines: no action yet, or last
  /// action was a yield.
  FOSTER_CORO_SUSPENDED_INACTIVE,
  FOSTER_CORO_RUNNING,
  FOSTER_CORO_DEAD
};

// We can't rely on assert() to print messages for us when we're
// not on the main thread's stack.
void coro_assert(bool ok, const char* msg) {
  if (!ok) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
  }
}

void foster_coro_wrapper_i32_i32(void* f_c) {
  foster_coro_i32_i32* fc = (foster_coro_i32_i32*) f_c;
  typedef int32_t(*fn_i32_i32)(void*, int32_t);
  fn_i32_i32 f = (fn_i32_i32) fc->fn;

  fc->sibling->arg = f(fc->env, fc->arg);
  fc->status = FOSTER_CORO_DEAD;
  coro_assert(false, "unexpectedly reached the end of a coroutine!");
  // hmm, want to clean up, which means ensuring that control flow
  // for the original thread returns to main(). what can we assume
  // is not corrupted?
}

// Transfer control from current coroutine to target coro,
// and mark target as being the current coroutine while remembering the prev.
int32_t coro_invoke_i32_i32(foster_generic_coro_i32_i32* gcoro, int32_t arg) {
   foster_coro_i32_i32* coro = (foster_coro_i32_i32*) gcoro;
   bool is_yielding = gcoro->fn == NULL;
   if (is_yielding) {
     coro_assert(coro->status = FOSTER_CORO_SUSPENDED_ACTIVE,
                 "can only yield to a suspended+active coroutine");
   } else {
     coro_assert(coro->status = FOSTER_CORO_SUSPENDED_INACTIVE,
                 "can only resume a suspended+inactive coroutine");
   }

   if (coro->sibling->pctx == NULL) {
     // hm, should this be done every call?
     coro->sibling->pctx = &coro_initial_contexts[0];
   }

   coro->arg = arg;
   coro->status = is_yielding ? FOSTER_CORO_INVALID
                              : FOSTER_CORO_RUNNING;
   coro->sibling->status = (is_yielding) ? FOSTER_CORO_SUSPENDED_INACTIVE
                                         : FOSTER_CORO_SUSPENDED_ACTIVE;

   // If there's no fn, it must mean we're yielding rather than invoking,
   // and we'll pop the stack when we reappear on the other side of the
   // call to foster_coro_transfer.
   if (!is_yielding) { current_coro.push_back(gcoro); }
   foster_coro_transfer(coro->sibling->pctx, coro->pctx);
   // Returning from a invoke means we're acting as a yield now,
   // and vice-versa.
   if (!is_yielding) { current_coro.pop_back(); }
   // So if we were originally yielding, then we are
   // now being re-invoked, possibly by a different
   // coro and/or a different thread!
   // But our sibling coro remains the same, it's just the
   // stack that it refers to that might have changed.
   coro->status = (is_yielding) ? FOSTER_CORO_SUSPENDED_ACTIVE
                                : FOSTER_CORO_SUSPENDED_INACTIVE;
   coro->sibling->status = (is_yielding) ? FOSTER_CORO_RUNNING
                                         : FOSTER_CORO_INVALID;
   return coro->sibling->arg;
}

// Transfer control from currently executing coroutine to its sibling,
// and mark the previous as being the new current.
int32_t coro_yield_i32_i32(int32_t arg) {
  coro_assert(!current_coro.empty(), "cannot yield before invoking a coroutine!");
  foster_generic_coro_i32_i32* coro = (foster_generic_coro_i32_i32*) current_coro.back();

  // The sibling we yield to should be suspended+active
  return coro_invoke_i32_i32((foster_generic_coro_i32_i32*) coro->sibling, arg);
}

foster_generic_coro_i32_i32*
coro_create_i32_i32(FosterClosurei32i32* pclo) {
  foster_coro_i32_i32* fcoro = (foster_coro_i32_i32*) memalloc(sizeof(foster_coro_i32_i32));
  foster_coro_i32_i32* ccoro = (foster_coro_i32_i32*) memalloc(sizeof(foster_coro_i32_i32));
  fcoro->pctx = foster_coro_create(foster_coro_wrapper_i32_i32, fcoro);

  // We don't fill in the sibling context pointer yet because
  // we don't know that the coro will be invoked by this thread...
  ccoro->pctx = NULL;
  fcoro->sibling = ccoro;
  ccoro->sibling = fcoro;
  fcoro->fn = pclo->code;
  fcoro->env = pclo->env;
  ccoro->fn  = NULL;
  ccoro->env = NULL;
  ccoro->status = FOSTER_CORO_INVALID;
  fcoro->status = FOSTER_CORO_SUSPENDED_INACTIVE;
  fcoro->arg = 555;
  ccoro->arg = 666;
  return (foster_generic_coro_i32_i32*) fcoro;
}


//////////////////////////////////////////////////////////////////

int force_gc_for_debugging_purposes() {
  gc::force_gc_for_debugging_purposes(); return 0;
}

int print_ref(void* x) {
  std::string fmt = gc::format_ref(x);
  return fprintf(stdout, "%s\n", fmt.c_str());
}

int  print_int(mp_int m) { return fprint_mp_int(stdout, m, 10); }
int expect_int(mp_int m) { return fprint_mp_int(stderr, m, 10); }
int  print_intx(mp_int m) { return fprint_mp_int(stdout, m, 16); }
int expect_intx(mp_int m) { return fprint_mp_int(stderr, m, 16); }
int  print_intb(mp_int m) { return fprint_mp_int(stdout, m, 2); }
int expect_intb(mp_int m) { return fprint_mp_int(stderr, m, 2); }

int  print_i32(int32_t x) { return fprint_i32(stdout, x); }
int expect_i32(int32_t x) { return fprint_i32(stderr, x); }

int  print_i32x(int32_t x) { return fprint_i32x(stdout, x); }
int expect_i32x(int32_t x) { return fprint_i32x(stderr, x); }

int  print_i32b(int32_t x) { return fprint_i32b(stdout, x); }
int expect_i32b(int32_t x) { return fprint_i32b(stderr, x); }

int read_i32() { int32_t n; scanf(" %d", &n); return n; }

int  print_i64(int64_t x) { return fprint_i64(stdout, x); }
int expect_i64(int64_t x) { return fprint_i64(stderr, x); }

//int  print_i8(char x) { return fprint_i8(stdout, x); }
//int expect_i8(char x) { return fprint_i8(stderr, x); }

// C type "bool" becomes LLVM "i8 zeroext", not "i1"
int  print_i1(bool x) { return fprintf(stdout, (x ? "true\n" : "false\n")); }
int expect_i1(bool x) { return fprintf(stderr, (x ? "true\n" : "false\n")); }
} // extern "C"
