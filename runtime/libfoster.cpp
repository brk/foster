// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifdef NDEBUG
#undef NDEBUG
#endif

#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS
#endif

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "libfoster.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "foster_gc_utils.h"

#include "base/atomicops.h"
#include "base/threading/simple_thread.h"

#ifdef OS_MACOSX
#include <objc/runtime.h>
#include <objc/objc-runtime.h>
#else
typedef void* id;
#endif

#include "cpuid.h"

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

struct AtomicBool {
  AtomicBool(bool val) : flag(val) {}

  void set(bool val) { base::subtle::Release_Store(&flag, val ? 1 : 0); }

  bool get() { return (base::subtle::Acquire_Load(&flag) > 0); }

private:
  volatile base::subtle::Atomic32 flag;
};

////////////////////////////////////////////////////////////////

const bool kUseSchedulingTimerThread = true;

struct FosterGlobals {
  int                    argc;
  char**                 argv;

  // One timer thread for the whole runtime, not per-vCPU.
  base::SimpleThread*    scheduling_timer_thread;
  id                     scheduling_timer_thread_autorelease_pool;

  cpuid_info             x86_cpuid_info;
};

FosterGlobals __foster_globals;

#ifdef OS_MACOSX
// http://stackoverflow.com/questions/11237579/how-to-create-a-nsautoreleasepool-without-objective-c
id allocAndInitAutoreleasePool() {
  id pool = class_createInstance((Class) objc_getClass("NSAutoreleasePool"), 0);
  return objc_msgSend(pool, sel_registerName("init"));
}

void drainAutoreleasePool(id pool) {
  (void)objc_msgSend(pool, sel_registerName("drain"));
}
#else
id allocAndInitAutoreleasePool() { return NULL; }
void drainAutoreleasePool(id pool) { return; }
#endif

////////////////////////////////////////////////////////////////////////////////

struct FosterVirtualCPU {
  FosterVirtualCPU() : needs_resched(0)
                     , current_coro(NULL)
                     {
    // Per-vCPU initialization...

    // Per the libcoro documentation, passing all zeros creates
    // an "empty" context which is suitable as an initial source
    // for coro_transfer.
    coro_create(&client_context, 0, 0, 0, 0);
  }

  ~FosterVirtualCPU() {
    foster_coro_destroy(&client_context);
  }

  //coro_context         runtime_context; // TODO...
  coro_context           client_context;

  // coro_invoke(c) sets this to c.
  // coro_yield() resets this to current_coro->invoker.
  foster_generic_coro*   current_coro;

  AtomicBool             needs_resched;
};

std::vector<FosterVirtualCPU*> __foster_vCPUs;

// {{{

inline FosterVirtualCPU* __foster_get_current_vCPU() {
  // TODO use TLS to store current vCPU?
  return __foster_vCPUs[0];
}

extern "C" foster_generic_coro** __foster_get_current_coro_slot() {
  return &(__foster_get_current_vCPU()->current_coro);
}

extern "C" void __foster_do_resched() {
  printf("__foster_do_resched...\n");
}

extern "C" bool __foster_need_resched_threadlocal() {
  FosterVirtualCPU* v = __foster_get_current_vCPU();
  if (v->needs_resched.get()) {
      v->needs_resched.set(false);
      return true;
  }
  return false;
}

// Rather than muck about with alarms, etc,
// we'll just use a dedicated sleepy thread.
class FosterSchedulingTimerThread : public base::SimpleThread {
 private:
  AtomicBool ending;

 public:
  virtual void Join() { // should only be called from main thread...
    ending.set(true);
    return base::SimpleThread::Join();
  }

  explicit FosterSchedulingTimerThread()
    : base::SimpleThread("foster.scheduling-timer-thread"), ending(false) {}
  virtual void Run() {
    while (!ending.get()) {
      const int ms = 1000;
      base::PlatformThread::Sleep(base::TimeDelta::FromMilliseconds(16));

      // Mark all execution contexts as needing rescheduling.
      __foster_get_current_vCPU()->needs_resched.set(true); // just one for now
    }
  }
};
// }}}

extern "C"
struct foster_bytes {
   int64_t cap;
   int8_t bytes[0];
};

// primitive defined by the compiler itself
extern "C" void* foster_emit_string_of_cstring(const char*, int32_t);

namespace foster {
namespace runtime {

  void start_scheduling_timer_thread() {
    if (kUseSchedulingTimerThread) {
      // Need to allocate an autorelease pool, or else the NSThread underlying
      // pthread underlying base::SimpleThread for our timer will be leaked.
      __foster_globals.scheduling_timer_thread_autorelease_pool
                                                  = allocAndInitAutoreleasePool();
      __foster_globals.scheduling_timer_thread = new FosterSchedulingTimerThread();
      __foster_globals.scheduling_timer_thread->Start();
    }
  }

  void finish_scheduling_timer_thread() {
    if (kUseSchedulingTimerThread) {
             __foster_globals.scheduling_timer_thread->Join();
      delete __foster_globals.scheduling_timer_thread;
      drainAutoreleasePool(__foster_globals.scheduling_timer_thread_autorelease_pool);
    }
  }

void initialize(int argc, char** argv) {
  __foster_globals.argc = argc;
  __foster_globals.argv = argv;

  cpuid_introspect(__foster_globals.x86_cpuid_info);
  //int cachesmall = cpuid_small_cache_size(__foster_globals.x86_cpuid_info);
  //int cachelarge = cpuid_large_cache_size(__foster_globals.x86_cpuid_info);

  // TODO Initialize one default coro context per thread.
  __foster_vCPUs.push_back(new FosterVirtualCPU());

  gc::initialize();
  start_scheduling_timer_thread();
}

int cleanup() {
  finish_scheduling_timer_thread();
  return gc::cleanup();
}


template <int N, typename Int>
int fprint_b2(FILE* f, Int x) {
  char* buf = new char[N+1];
  buf[N] = '\0';
  for (Int i = 0; i < N; ++i) {
    buf[(N-1) - i] = (x & (Int(1)<<i)) ? '1' : '0';
  }
  int n = fprintf(f, "%s_2\n", buf);
  delete [] buf;
  return n;
}

void fprint_f64(FILE* f, double x) { fprintf(f, "%f\n", x); }
void fprint_p9f64(FILE* f, double x) { fprintf(f, "%.9f\n", x); }

void fprint_i64(FILE* f, int64_t x) { fprintf(f, "%" PRId64 "\n", x); }
void fprint_i64x(FILE* f, int64_t x) { fprintf(f, "%" PRIX64 "_16\n", x); }
void fprint_i64b(FILE* f, int64_t x) { fprint_b2<64>(f, x); }
void fprint_i64_bare(FILE* f, int64_t x) { fprintf(f, "%" PRId64 , x); }

void fprint_i32(FILE* f, int32_t x) {  fprintf(f, "%d\n", x); fflush(f); }
void fprint_i32x(FILE* f, int32_t x) { fprintf(f, "%X_16\n", x); }
void fprint_i32b(FILE* f, int32_t x) { fprint_b2<32>(f, x); }

void fprint_i8b(FILE* f, int8_t x) { fprint_b2<8>(f, x); }

void fprint_bytes(FILE* f, foster_bytes* array, uint32_t n) {
  uint32_t c = array->cap;
  fprintf(f, "%.*s", (std::min)(n, c), &array->bytes[0]);
}

} } // namespace foster::runtime

using namespace foster::runtime;

extern "C" {

//////////////////////////////////////////////////////////////////

void foster__assert_failed(const char* msg) {
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  exit(1);
}

void foster__assert(bool ok, const char* msg) {
  if (!ok) {
    foster__assert_failed(msg);
  }
}

void foster__abort() {
  foster__assert_failed("foster__abort called");
}

__attribute__((noinline))
void foster__boundscheck64_failed(int64_t idx, int64_t len, const char* srclines) {
  fprintf(stderr, "bounds check failed: cannot index array of "
                  "length %" PRId64 " (0x%" PRIX64 ") with value %" PRId64 " (0x%" PRIX64 ")\n"
                  "%s", len, len, idx, idx, srclines);
  fflush(stderr);
  exit(1);
}

void foster__boundscheck64(int64_t idx, int64_t len, const char* srclines) {
  if (idx < 0 || idx >= len) {
    foster__boundscheck64_failed(idx, len, srclines);
  }
}

int force_gc_for_debugging_purposes() {
  gc::force_gc_for_debugging_purposes(); return 0;
}

void  print_i8(int8_t x) { fprint_i32(stdout, x); } // implicit conversion
void expect_i8(int8_t x) { fprint_i32(stderr, x); } // implicit conversion

void  print_i8b(int8_t x) { fprint_i8b(stdout, x); }
void expect_i8b(int8_t x) { fprint_i8b(stderr, x); }

void  print_i32(int32_t x) { fprint_i32(stdout, x); }
void expect_i32(int32_t x) { fprint_i32(stderr, x); }

void  print_i32x(int32_t x) { fprint_i32x(stdout, x); }
void expect_i32x(int32_t x) { fprint_i32x(stderr, x); }

void  print_i32b(int32_t x) { fprint_i32b(stdout, x); }
void expect_i32b(int32_t x) { fprint_i32b(stderr, x); }

int read_i32() { int32_t n; scanf(" %d", &n); return n; }

void  print_i64_bare(int64_t x) { fprint_i64_bare(stdout, x); }
void  print_i64(int64_t x) { fprint_i64(stdout, x); }
void expect_i64(int64_t x) { fprint_i64(stderr, x); }
void  print_i64x(int64_t x) { fprint_i64x(stdout, x); }
void expect_i64x(int64_t x) { fprint_i64x(stderr, x); }

void  print_i64b(int64_t x) { fprint_i64b(stdout, x); }
void expect_i64b(int64_t x) { fprint_i64b(stderr, x); }

// C type "bool" becomes LLVM "i8 zeroext", not "i1"
void  print_i1(bool x) { fprintf(stdout, (x ? "true\n" : "false\n")); }
void expect_i1(bool x) { fprintf(stderr, (x ? "true\n" : "false\n")); }

// This is used by the compiler.
uint8_t foster_ctor_id_of(void* body) {
  return foster::runtime::ctor_id_of(body);
}

void print_addr(void* x) { fprintf(stdout, "addr: %p\n", x); }

void print_newline()  { fprintf(stdout, "\n"); }
void expect_newline() { fprintf(stderr, "\n"); }

void prim_print_bytes_stdout(foster_bytes* array, uint32_t n) {
  fprint_bytes(stdout, array, n);
}

void prim_print_bytes_stderr(foster_bytes* array, uint32_t n) {
  fprint_bytes(stderr, array, n);
}

void memcpy_i8_to_from_at_len(foster_bytes* to, foster_bytes* from,
                              uint32_t req_at, uint32_t req_len) {
  // Note: from->cap is represented as i64 but for now there's an
  // invariant that its value is representable using (signed) i32,
  // so the truncation from int64_t to uint32_t is OK.
  if (uint32_t(from->cap) < req_at) {
    foster__assert(false,
                   "memcpy_i8_to_from_at_len can't copy negative # of bytes!");
  } else {
    int32_t from_rem = uint32_t(from->cap) - req_at;
    req_len =      (std::min)(req_len, uint32_t(to->cap));
    uint32_t len = (std::min)(uint32_t(from_rem), req_len);
    memcpy(to->bytes, from->bytes + req_at, len);
  }
}

void memcpy_i8_to_at_from_len(foster_bytes* to,   uint32_t req_at,
                              foster_bytes* from, uint32_t req_len) {
  // Note: to->cap is represented as i64 but for now there's an
  // invariant that its value is representable using (signed) i32,
  // so the truncation from int64_t to uint32_t is OK.
  if (uint32_t(to->cap) < req_at) {
    foster__assert(false,
                   "memcpy_i8_to_from_at_len can't copy negative # of bytes!");
  } else {
    int32_t to_rem = uint32_t(to->cap) - req_at;
    req_len =      (std::min)(req_len, uint32_t(from->cap));
    uint32_t len = (std::min)(uint32_t(to_rem), req_len);
    memcpy(to->bytes + req_at, from->bytes, len);
  }
}

void print_float_p9f64(double f) { return fprint_p9f64(stdout, f); }
void expect_float_p9f64(double f) { return fprint_p9f64(stderr, f); }

// For GC roots to work correctly, the returned pointer
// must be of type Text (i.e. %Text.DT*) but we have no
// way of naming that type here. So we wrap this function
// as get_cmdline_arg_n(n) in CodegenUtils.cpp.
void* foster_get_cmdline_arg_n_raw(int32_t n) {
  if (n >= 0  &&  n < __foster_globals.argc) {
      const char* s = __foster_globals.argv[n];
      return foster_emit_string_of_cstring(s, strlen(s));
  } else {
      const char* s = "";
      return foster_emit_string_of_cstring(s, 0);
  }
}

extern int32_t opaquely_i32(int32_t n);

// Provided by third_party/fftw/cycle_wrapper.c
extern int64_t __foster_getticks();
extern double  __foster_getticks_elapsed(int64_t t1, int64_t t2);

int64_t foster_getticks() { return __foster_getticks(); }
double  foster_getticks_elapsed(int64_t t1, int64_t t2) {
  return __foster_getticks_elapsed(t1, t2);
}

// http://stackoverflow.com/questions/4308996/finding-the-address-range-of-the-data-segment

// We want to perform aggressive link time optimization of
// foster code + stdlib, without having runtime::initialize()
// and ::cleanup() discarded. This function is hardcoded to be
// a LTO root, since libfoster_main is compiled straight to .o, not .bc,
//  which is why it doesn't contribute to their non-deadness.
extern "C" int foster__main();
extern "C" void foster_coro_delete_self_reference(void* vc);

int foster__runtime__main__wrapper(int argc, char** argv) {
  bool tru = opaquely_i32(0) == 0;

  foster::runtime::initialize(argc, argv);
  foster__main();

  if (!tru) {
    // kung-fu grip to prevent LTO from being too mean.
    foster_coro_delete_self_reference((void*)&foster__gcmaps);
  }

  return foster::runtime::cleanup();
}

} // extern "C"

