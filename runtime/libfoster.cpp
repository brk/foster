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
#include <cerrno>
#include <cstdlib>
#include <vector>
#include <cmath>

#include "libfoster.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "foster_gc_utils.h"
#include "foster_globals.h"

#include "base/atomicops.h"
#include "base/time/time.h"

#include <signal.h>

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

extern "C" void foster__assert(bool ok, const char* msg);

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

FosterGlobals __foster_globals;

struct FosterVirtualCPU;
std::vector<FosterVirtualCPU*> __foster_vCPUs;

////////////////////////////////////////////////////////////////////////////////

void __foster_handle_sigsegv(int, siginfo_t* si, void*) {
  fprintf(stdout,
          "ERROR: Foster runtime caught SIGSEGV at addr %p, aborting!\n",
          si->si_addr);

  bool is_stable = foster::runtime::gc::is_marked_as_stable((foster::runtime::gc::tori*) si->si_addr);
  if (is_stable) {
    fprintf(stdout, "This address appears to be within the bounds of the stack or the program's data section.\n");
  }
  fflush(stdout);
  exit(2);
}

void __foster_install_sigsegv_handler() {
  struct sigaction sa = {
      .sa_sigaction = __foster_handle_sigsegv,
      .sa_flags     = SA_ONSTACK | SA_SIGINFO,
      .sa_mask      = 0,
  };
  int rv;
  rv = sigfillset(&sa.sa_mask); // block all other signals
  foster__assert(rv == 0, "sigfillset failed");

  rv = sigaction(SIGSEGV, &sa, NULL);
  foster__assert(rv == 0, "installing SIGSEGV fault handler failed");
}

////////////////////////////////////////////////////////////////////////////////

struct FosterVirtualCPU {
  FosterVirtualCPU() : needs_resched(0)
                     , current_coro(NULL)
                     , signal_stack(NULL)
                     {
    // Per-vCPU initialization...

    // Per the libcoro documentation, passing all zeros creates
    // an "empty" context which is suitable as an initial source
    // for coro_transfer.
    coro_create(&client_context, 0, 0, 0, 0);
  }

  ~FosterVirtualCPU() {
    foster_coro_destroy(&client_context);
    free(signal_stack);
  }

  void install_signal_stack() {
    signal_stack = malloc(SIGSTKSZ);
    foster__assert(signal_stack, "signal stack allocation failed");
    stack_t ss = {
        .ss_size = SIGSTKSZ,
        .ss_sp = signal_stack,
        .ss_flags = 0,
    };
    int rv = sigaltstack(&ss, NULL);
    foster__assert(rv == 0, "signaltstack failed");
  }

  //coro_context         runtime_context; // TODO...
  coro_context           client_context;

  // coro_invoke(c) sets this to c.
  // coro_yield() resets this to current_coro->invoker.
  foster_generic_coro*   current_coro;

  AtomicBool             needs_resched;

  void*                  signal_stack;
};

// {{{

inline static FosterVirtualCPU* __foster_get_current_vCPU() {
  // TODO use TLS to store current vCPU?
  return __foster_vCPUs[0];
}

extern "C" foster_generic_coro** __foster_get_current_coro_slot() {
  return &(__foster_get_current_vCPU()->current_coro);
}

// $ gotest.sh speed/siphash --optc-arg=-foster-insert-timing-checks --backend-optimize
// $ test-tmpdir/siphash/siphash 64 20048
extern "C" void __foster_do_resched() {
  FosterVirtualCPU* v = __foster_get_current_vCPU();
  v->needs_resched.set(false);
  printf("__foster_do_resched...\n");
}

extern "C" bool __foster_need_resched_threadlocal() {
  FosterVirtualCPU* v = __foster_get_current_vCPU();
  return v->needs_resched.get();
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

// primitive defined by the compiler itself
extern "C" void* foster_emit_string_of_cstring(const char*, int32_t);

namespace foster {
namespace runtime {

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

void initialize(int argc, char** argv, void* stack_base) {
  parse_runtime_options(argc, argv);

  // TODO Initialize one default coro context per thread.
  __foster_vCPUs.push_back(new FosterVirtualCPU());
  __foster_vCPUs[0]->install_signal_stack();

  __foster_install_sigsegv_handler();

  gc::initialize(stack_base);
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
  int n = fprintf(f, "0b%s\n", buf);
  delete [] buf;
  return n;
}

void fprint_f64(FILE* f, double x) { fprintf(f, "%f\n", x); }
void fprint_f64x(FILE* f, double x) { fprintf(f, "%a\n", x); }
void fprint_p9f64(FILE* f, double x) { fprintf(f, "%.9f\n", x); }
// TODO .17g for doubles?

void fprint_i64(FILE* f, int64_t x) { fprintf(f, "%" PRId64 "\n", x); }
void fprint_i64x(FILE* f, int64_t x) { fprintf(f, "0x%" PRIX64 "\n", x); }
void fprint_i64b(FILE* f, int64_t x) { fprint_b2<64>(f, x); }
void fprint_i64_bare(FILE* f, int64_t x) { fprintf(f, "%" PRId64 , x); }

void fprint_i32(FILE* f, int32_t x) {  fprintf(f, "%d\n", x); fflush(f); }
void fprint_i32x(FILE* f, int32_t x) { fprintf(f, "0x%X\n", x); }
void fprint_i32b(FILE* f, int32_t x) { fprint_b2<32>(f, x); }

void fprint_i8b(FILE* f, int8_t x) { fprint_b2<8>(f, x); }

void fprint_bytes_from(FILE* f, foster_bytes* array, uint32_t n, uint32_t off) {
  uint32_t c = array->cap;
  uint32_t lim = (std::min)(n + off, c);
  // If (n + off) overflows, then lim < off,
  if (lim > off) {
    uint32_t size = lim - off;
    fprintf(f, "%.*s", size, &array->bytes[off]);
  }
}

template<typename T>
T min3(T a, T b, T c) { return (std::min)(  (std::min)(a, b),  c); }

} } // namespace foster::runtime

using namespace foster::runtime;

extern "C" {

//////////////////////////////////////////////////////////////////

__attribute__((noinline))
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
  // We have the invariant that len > 0 (as a signed value), which means that
  // (idx < 0 || idx >= len) has the same result as (idx >=u len)
  if (uint64_t(idx) >= uint64_t(len)) {
    foster__boundscheck64_failed(idx, len, srclines);
  }
}

int32_t force_gc_for_debugging_purposes() {
  gc::force_gc_for_debugging_purposes(); return 0;
}

void  print_i8(int8_t x) { fprint_i32(stdout, x); } // implicit conversion
void expect_i8(int8_t x) { fprint_i32(stderr, x); } // implicit conversion

void  print_i8x(int8_t x) { fprint_i32x(stdout, uint8_t(x)); }
void expect_i8x(int8_t x) { fprint_i32x(stderr, uint8_t(x)); }

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

void prim_print_bytes_stdout(foster_bytes* array, uint32_t n, uint32_t off) {
  fprint_bytes_from(stdout, array, n, off);
}

void prim_print_bytes_stderr(foster_bytes* array, uint32_t n, uint32_t off) {
  fprint_bytes_from(stderr, array, n, off);
}

// to[0..req_len] = from[req_at..req_at+req_len]
void memcpy_i8_to_from_at_len(foster_bytes* to, foster_bytes* from,
                              uint32_t req_at, uint32_t req_len) {
  // Note: from->cap is represented as i64 but for now there's an
  // invariant that its value is representable using (signed) i32,
  // so the truncation from int64_t to uint32_t is OK.
  foster__assert(uint32_t(from->cap) >= req_at,
                 "memcpy_i8_to_from_at_len can't copy negative # of bytes!");
  foster__assert(to != from, "memcpy_i8_to_at_from_len: arrays must not be aliased");
  int32_t from_rem = uint32_t(from->cap) - req_at;
  req_len =      (std::min)(req_len, uint32_t(to->cap));
  uint32_t len = (std::min)(uint32_t(from_rem), req_len);
  memcpy(to->bytes, from->bytes + req_at, len);
}

// to[req_at..whatever] = from[0..req_len]
void memcpy_i8_to_at_from_len(foster_bytes* to,   uint32_t req_at,
                              foster_bytes* from, uint32_t req_len) {
  // Note: to->cap is represented as i64 but for now there's an
  // invariant that its value is representable using (signed) i32,
  // so the truncation from int64_t to uint32_t is OK.
  foster__assert(uint32_t(to->cap) >= req_at,
                             "memcpy_i8_to_from_at_len can't copy negative # of bytes!");
  foster__assert(to != from, "memcpy_i8_to_at_from_len: arrays must not be aliased");
  int32_t to_rem = uint32_t(to->cap) - req_at;
  req_len =      (std::min)(req_len, uint32_t(from->cap));
  uint32_t len = (std::min)(uint32_t(to_rem), req_len);
  memcpy(to->bytes + req_at, from->bytes, len);
}

// to[to_at..to_at+req_len] = from[from_at..from_at+req_len]
// (or as close of a slice as possible)
// Returns 0 if the requested number of bytes were copied, 1 otherwise.
int8_t memcpy_i8_to_at_from_at_len(foster_bytes* to,   int64_t   to_at,
                                   foster_bytes* from, int64_t from_at,
                                   int64_t req_len) {
  foster__assert((from->cap >= from_at) && (to->cap >= to_at),
                             "memcpy_i8_to_at_from_at_len can't copy negative # of bytes!");
  foster__assert(to != from, "memcpy_i8_to_at_from_at_len: arrays must not be aliased");
  // guaranteed to be non-negative due to assertion invariant
  int64_t   to_rem = to->cap   - to_at;
  int64_t from_rem = from->cap - from_at;
  int64_t len = min3(to_rem, from_rem, req_len);
  size_t  len_sz = len;
  foster__assert(len >= 0 && int64_t(len_sz) == len, "memcpy_i8_to_from_at_len can't copy that many bytes on this platform!");
  memcpy(to->bytes + to_at, from->bytes + from_at, len_sz);
  return (len == req_len) ? 0 : 1;
}

void print_float_f64x(double f) { return fprint_f64x(stdout, f); }
void expect_float_f64x(double f) { return fprint_f64x(stderr, f); }

void print_float_p9f64(double f) { return fprint_p9f64(stdout, f); }
void expect_float_p9f64(double f) { return fprint_p9f64(stderr, f); }

double foster__logf64(double f) { return log(f); }

// For GC roots to work correctly, the returned pointer
// must be of type Text (i.e. %Text.DT*) but we have no
// way of naming that type here. So we wrap this function
// as get_cmdline_arg_n(n) in CodegenUtils.cpp.
void* foster_get_cmdline_arg_n_raw(int32_t n) {
  if (n >= 0  &&  n < __foster_globals.args.size()) {
      const char* s = __foster_globals.args[n];
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

// Re-implementation of the ``secs`` function from Criterion.Measurement
// (temporary expedient because we don't have much in the way of facilities
//  for working with double values within foster yet...)
// http://hackage.haskell.org/package/criterion which is under the BSD3 license.
void* foster_fmttime_secs_raw(double secs) {
  char buf[64] = { 0 };
  char* ptr = &buf[0];
  const char* unit = "s"; bool small = false;
  if (secs < 0.0) { *ptr++ = '-'; secs = -secs; }

       if (secs >= 1.0) { }
  else if (secs >= 1e-3 ) { unit = "ms"; secs *= 1e3 ; }
  else if (secs >= 1e-6 ) { unit = "μs"; secs *= 1e6 ; }
  else if (secs >= 1e-9 ) { unit = "ns"; secs *= 1e9 ; }
  else if (secs >= 1e-12) { unit = "ps"; secs *= 1e12; }
  else if (secs >= 1e-15) { unit = "fs"; secs *= 1e15; }
  else if (secs >= 1e-18) { unit = "as"; secs *= 1e18; }
  else { small = true; }

       if (secs == 0.0) { snprintf(ptr, 63, "0.0 s"); } // for Haskell compatibility...
  else if (small)       { snprintf(ptr, 63, "%g s", secs); }
  else if (secs >= 1e9) { snprintf(ptr, 63, "%.4g %s", secs, unit); }
  else if (secs >= 1e3) { snprintf(ptr, 63, "%.0f %s", secs, unit); }
  else if (secs >= 1e2) { snprintf(ptr, 63, "%.1f %s", secs, unit); }
  else if (secs >= 1e1) { snprintf(ptr, 63, "%.2f %s", secs, unit); }
  else                  { snprintf(ptr, 63, "%.3f %s", secs, unit); }

  return foster_emit_string_of_cstring(buf, strlen(buf));
}

int64_t foster_gettime_microsecs() {
  return base::TimeTicks::Now().ToInternalValue();
}
double  foster_gettime_elapsed_secs(int64_t early, int64_t later) {
  return base::TimeDelta::FromMicroseconds(later - early).InSecondsF();
}

// We want to perform aggressive link time optimization of
// foster code + stdlib, without having runtime::initialize()
// and ::cleanup() discarded. This function is hardcoded to be
// a LTO root, since libfoster_main is compiled straight to .o, not .bc,
//  which is why it doesn't contribute to their non-deadness.
extern "C" int foster__main();
extern "C" void foster_coro_delete_self_reference(void* vc);

int foster__runtime__main__wrapper(int argc, char** argv) {
  bool tru = opaquely_i32(0) == 0;

  foster::runtime::initialize(argc, argv, (void*) &tru);
  foster__main();

  if (!tru) {
    // kung-fu grip to prevent LTO from being too mean.
    foster_coro_delete_self_reference((void*)&foster__gcmaps);
  }

  return foster::runtime::cleanup();
}

} // extern "C"

