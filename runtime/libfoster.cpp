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
#include <cmath>

#include <string>

#include "libfoster.h"
#include "libfoster_util.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "foster_gc_utils.h"
#include "foster_globals.h"

#include "crypto_hash_sha256.h"

#define ENABLE_CLOCKTIMER 1
#include "clocktimer.h"

#include <signal.h>

////////////////////////////////////////////////////////////////

extern "C" void foster__assert(bool ok, const char* msg);

////////////////////////////////////////////////////////////////

const bool kUseSchedulingTimerThread = false;

FosterGlobals __foster_globals;

////////////////////////////////////////////////////////////////////////////////

void __foster_handle_sigsegv(int, siginfo_t* si, void*) {
  fprintf(stdout,
          "ERROR: Foster runtime caught SIGSEGV at addr %p, aborting!\n",
          si->si_addr);

  fflush(stdout);
  exit(2);
}

void __foster_install_sigsegv_handler() {
  struct sigaction sa = {
      .sa_mask      = 0,
      .sa_flags     = SA_ONSTACK | SA_SIGINFO,
  };
  sa.sa_sigaction = __foster_handle_sigsegv;
  int rv;
  rv = sigfillset(&sa.sa_mask); // block all other signals
  foster__assert(rv == 0, "sigfillset failed");

  rv = sigaction(SIGSEGV, &sa, NULL);
  foster__assert(rv == 0, "installing SIGSEGV fault handler failed");
}

////////////////////////////////////////////////////////////////////////////////

// The default coro struct should be dynamically allocated;
// if it is statically allocated then it will be ignored by the
// subheap-crossing filter in immix_trace().
extern "C" foster_bare_coro* foster__runtime__alloc_default_coro();

struct FosterVirtualCPU {
  FosterVirtualCPU() : needs_resched(0)
                     , current_coro(NULL)
                     , signal_stack(NULL)
                     {}

  ~FosterVirtualCPU() {
    foster_coro_destroy(&current_coro->ctx);
    free(signal_stack);
  }

  void default_coro_setup() {
    current_coro = foster__runtime__alloc_default_coro();
    // Per the libcoro documentation, passing all zeros creates
    // an "empty" context which is suitable as an initial source
    // for coro_transfer.
    libcoro__coro_create(&current_coro->ctx, 0, 0, 0, 0);
    current_coro->env = NULL;
    current_coro->parent = NULL;
    current_coro->indirect_self = NULL;
    current_coro->status = FOSTER_CORO_RUNNING;
  }

  void install_signal_stack() {
    signal_stack = malloc(SIGSTKSZ);
    foster__assert(signal_stack, "signal stack allocation failed");
    stack_t ss = {
        .ss_sp = signal_stack,
        .ss_flags = 0,
        .ss_size = SIGSTKSZ,
    };
    int rv = sigaltstack(&ss, NULL);
    foster__assert(rv == 0, "signaltstack failed");
  }

  // Updated by coro_invoke and coro_yield.
  foster_bare_coro*      current_coro;

  std::atomic<bool>      needs_resched;

  void*                  signal_stack;
};

// {{{

FosterVirtualCPU* foster__current_vCPU = nullptr;

extern "C" foster_bare_coro** __foster_get_current_coro_slot() {
  return &(foster__current_vCPU->current_coro);
}

// $ gotest.sh speed/siphash --optc-arg=-foster-insert-timer-checks --backend-optimize
// $ test-tmpdir/siphash/siphash 64 20048
extern "C" void __foster_do_resched() {
  foster__current_vCPU->needs_resched.store(false);
  printf("__foster_do_resched...\n");
}

extern "C" bool __foster_need_resched_threadlocal() {
  return foster__current_vCPU->needs_resched.load();
}

// Rather than muck about with alarms, etc,
// we'll just use a dedicated sleepy thread.
void fosterSchedulingTimerThread(std::atomic<bool>& ending) {
  while (!ending.load()) {
    const int ms = 1000;
    std::this_thread::sleep_for(std::chrono::milliseconds(500));
    printf("fosterSchedulingTimerThread\n");

    // Mark all execution contexts as needing rescheduling.
    foster__current_vCPU->needs_resched.store(true); // just one for now
  }
};
// }}}

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
      __foster_globals.scheduling_timer_thread_ending.store(false);
      __foster_globals.scheduling_timer_thread = new std::thread(
            fosterSchedulingTimerThread,
            std::ref(__foster_globals.scheduling_timer_thread_ending));
    }
  }

  void finish_scheduling_timer_thread() {
    if (kUseSchedulingTimerThread) {
      __foster_globals.scheduling_timer_thread_ending.store(true);
             __foster_globals.scheduling_timer_thread->join();
      delete __foster_globals.scheduling_timer_thread;
      drainAutoreleasePool(__foster_globals.scheduling_timer_thread_autorelease_pool);
    }
  }

void initialize(int argc, char** argv, void* stack_base) {
  parse_runtime_options(argc, argv);

  gc::initialize(stack_base);

  foster__current_vCPU = new FosterVirtualCPU();
  foster__current_vCPU->default_coro_setup();
  foster__current_vCPU->install_signal_stack();

  __foster_install_sigsegv_handler();

  start_scheduling_timer_thread();
}

int cleanup() {
  finish_scheduling_timer_thread();
  return gc::cleanup();
}

void fprint_f32(FILE* f, float x) { fprintf(f, "%f\n", x); }
void fprint_f32_bare(FILE* f, float x) { fprintf(f, "%f", x); }
void fprint_f32x(FILE* f, float x) { fprintf(f, "%a\n", x); }
void fprint_f64(FILE* f, double x) { fprintf(f, "%f\n", x); }
void fprint_f64_bare(FILE* f, double x) { fprintf(f, "%f", x); }
void fprint_f64x(FILE* f, double x) { fprintf(f, "%a\n", x); }
void fprint_p9f64(FILE* f, double x) { fprintf(f, "%.9f\n", x); }
// TODO .17g for doubles?

void fprint_i64(FILE* f, int64_t x) { fprintf(f, "%" PRId64 "\n", x); }

void fprint_bytes_from(FILE* f, foster_bytes* array, uint32_t n, uint32_t off) {
  uint32_t c = array->cap;
  uint32_t lim = (std::min)(n + off, c);
  // If (n + off) overflows, then lim < off,
  if (lim > off) {
    uint32_t count = lim - off;
    fwrite(&array->bytes[off], 1, count, f);
  }
}

template<typename T>
T min3(T a, T b, T c) { return (std::min)(  (std::min)(a, b),  c); }

} } // namespace foster::runtime

using namespace foster::runtime;

extern "C" {

//////////////////////////////////////////////////////////////////

// Int is represented (opaquely) as a inversely-tagged pointer.
typedef void* Int;
// A 0 in the low bit signifies a pointer to a bignum.
// A 1 in the low bit signifies a (signed) 63-bit integer
// in the high bits.
// Thus a "small" integer K is represented as 2K + 1,
// with the restriction that K fits in 63 bits. A signed 64-bit integer
// S is small if the top two bits of S are both zero or both one.
//
// Using 0 for pointers and 1 for integers makes it easier for the
// GC to recognize when a potential-reference cell is actually a
// short int.

// Precondition: Int-isSmallWord(x)
Int foster_prim_smallWord_to_Int(intptr_t x) { return (Int)uintptr_t((x << 1) | 1); }

// Precondition: foster_prim_Int_isSmall(x)
intptr_t foster_prim_Int_to_smallWord(Int x) { return intptr_t(x) >> 1; }

bool foster_prim_Int_isSmall(Int x) { return (uintptr_t(x) & 1) == 1; }

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

// Emitted by emitFosterArrayBoundsCheck() in CodegenUtils.cpp
// which is in turn called by getArraySlot(); the len parameter
// is calculated by tryBindArray().
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

void  print_i64(int64_t x) { fprint_i64(stdout, x); }
void expect_i64(int64_t x) { fprint_i64(stderr, x); }

// C type "bool" becomes LLVM "i8 zeroext", not "i1"

// This is used by the compiler.
uint8_t foster_ctor_id_of(void* body) {
  return foster::runtime::ctor_id_of(body);
}

void print_addr(void* x) { fprintf(stdout, "addr: %p\n", x); }

void prim_print_bytes_stdout(foster_bytes* array, uint32_t n, uint32_t off) {
  fprint_bytes_from(stdout, array, n, off);
}

void prim_print_bytes_stderr(foster_bytes* array, uint32_t n, uint32_t off) {
  fprint_bytes_from(stderr, array, n, off);
}

// to[to_at..to_at+req_len] = from[from_at..from_at+req_len]
// (or as close of a slice as possible)
// Returns the number of *un*copied bytes.
int64_t memcpy_i8_to_at_from_at_len(foster_bytes* to,   int64_t   to_at,
                                    foster_bytes* from, int64_t from_at,
                                    int64_t req_len) {
  foster__assert((from->cap >= from_at) && (to->cap >= to_at),
                             "memcpy_i8_to_at_from_at_len can't copy negative # of bytes!");
  // guaranteed to be non-negative due to assertion invariant
  int64_t   to_rem = to->cap   - to_at;
  int64_t from_rem = from->cap - from_at;
  int64_t len = min3(to_rem, from_rem, req_len);
  size_t  len_sz = len;
  foster__assert(len >= 0 && int64_t(len_sz) == len, "memcpy_i8_to_from_at_len can't copy that many bytes on this platform!");
  if (to != from) {
    memcpy(to->bytes + to_at, from->bytes + from_at, len_sz);
  } else {
    memmove(to->bytes + to_at, from->bytes + from_at, len_sz);
  }
  return req_len - len;
}

int8_t foster_crypto_hash_sha256(foster_bytes* output, foster_bytes* input) {
  if (output->cap != crypto_hash_sha256_BYTES) {
    return 1;
  }
  return crypto_hash_sha256(reinterpret_cast<unsigned char*>(output->bytes),
                            reinterpret_cast<const unsigned char*>(input->bytes),
                            input->cap); // returns zero
}

void print_f32_bare(float f) { return fprint_f32_bare(stdout, f); }
void expect_f32_bare(float f) { return fprint_f32_bare(stderr, f); }

void print_f64_bare(double f) { return fprint_f64_bare(stdout, f); }
void expect_f64_bare(double f) { return fprint_f64_bare(stderr, f); }

void print_float_f32(float f) { return fprint_f32(stdout, f); }
void expect_float_f32(float f) { return fprint_f32(stderr, f); }
void print_float_f32x(float f) { return fprint_f32x(stdout, f); }

void print_float_f64(double f) { return fprint_f64(stdout, f); }
void expect_float_f64(double f) { return fprint_f64(stderr, f); }

void print_float_f64x(double f) { return fprint_f64x(stdout, f); }
void expect_float_f64x(double f) { return fprint_f64x(stderr, f); }

void print_float_p9f64(double f) { return fprint_p9f64(stdout, f); }
void expect_float_p9f64(double f) { return fprint_p9f64(stderr, f); }

double foster__logf64(double f) { return log(f); }

float  foster__tanf32(float  f) { return tanf(f); }
double foster__tanf64(double f) { return tan(f); }

double foster__powf64(double x, double y) { return pow(x, y); }

int32_t get_cmdline_n_args() { return __foster_globals.args.size(); }

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

// Provided by third_party/fftw_cycle/cycle-wrapper.cpp
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
void foster_fmttime_secs_ptr(double secs, char* ptr) {
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

       if (secs == 0.0) { snprintf(ptr, 62, "0.0 s"); } // for Haskell compatibility...
  else if (small)       { snprintf(ptr, 62, "%g s", secs); }
  else if (secs >= 1e9) { snprintf(ptr, 62, "%.4g %s", secs, unit); }
  else if (secs >= 1e3) { snprintf(ptr, 62, "%.0f %s", secs, unit); }
  else if (secs >= 1e2) { snprintf(ptr, 62, "%.1f %s", secs, unit); }
  else if (secs >= 1e1) { snprintf(ptr, 62, "%.2f %s", secs, unit); }
  else                  { snprintf(ptr, 62, "%.3f %s", secs, unit); }

}

void* foster_fmttime_secs_raw(double secs) {
  char buf[64] = { 0 };
  foster_fmttime_secs_ptr(secs, &buf[0]);
  return foster_emit_string_of_cstring(buf, strlen(buf));
}

// ptr should be a pointer to a char buf[64]
void foster__humanize_s_ptr(double val, char* ptr, const char* unit) {
  const char* prefix = ""; bool extreme = false;
  if (val < 0.0) { *ptr++ = '-'; val = -val; }

       if (val >= 1e21) { extreme = true; }
  else if (val >= 1e18 ) { prefix = "E"; val *= 1e-18; }
  else if (val >= 1e15 ) { prefix = "P"; val *= 1e-15; }
  else if (val >= 1e12 ) { prefix = "T"; val *= 1e-12; }
  else if (val >= 1e9 )  { prefix = "G"; val *= 1e-9 ; }
  else if (val >= 1e6 )  { prefix = "M"; val *= 1e-6 ; }
  else if (val >= 1e3 )  { prefix = "K"; val *= 1e-3 ; }
  else if (val >= 0   )  { }
  else if (val >= 1e-3 ) { prefix = "m"; val *= 1e3 ; }
  else if (val >= 1e-6 ) { prefix = "μ"; val *= 1e6 ; }
  else if (val >= 1e-9 ) { prefix = "n"; val *= 1e9 ; }
  else if (val >= 1e-12) { prefix = "p"; val *= 1e12; }
  else if (val >= 1e-15) { prefix = "f"; val *= 1e15; }
  else if (val >= 1e-18) { prefix = "a"; val *= 1e18; }
  else { extreme = true; }

       if (val == 0.0) { snprintf(ptr, 62, "0.0 %s", unit); } // for Haskell compatibility...
  else if (extreme)    { snprintf(ptr, 62, "%g %s", val, unit); }
  else if (val >= 1e9) { snprintf(ptr, 62, "%.4g %s%s", val, prefix, unit); }
  else if (val >= 1e3) { snprintf(ptr, 62, "%.0f %s%s", val, prefix, unit); }
  else if (val >= 1e2) { snprintf(ptr, 62, "%.1f %s%s", val, prefix, unit); }
  else if (val >= 1e1) { snprintf(ptr, 62, "%.2f %s%s", val, prefix, unit); }
  else                 { snprintf(ptr, 62, "%.3f %s%s", val, prefix, unit); }
}

void* foster_humanize_s(double val) {
  char buf[64] = { 0 };
  foster__humanize_s_ptr(val, &buf[0], "");
  return foster_emit_string_of_cstring(buf, strlen(buf));
}



int64_t foster_gettime_microsecs() {
  return clocktimer<true>::current_us();
}
double  foster_gettime_elapsed_secs(int64_t early, int64_t later) {
  return double(later - early) / 1e6;
}

// We want to perform aggressive link time optimization of
// foster code + stdlib, without having runtime::initialize()
// and ::cleanup() discarded. This function is hardcoded to be
// a LTO root, since libfoster_main is compiled straight to .o, not .bc,
//  which is why it doesn't contribute to their non-deadness.
extern "C" int foster__main();
extern "C" void foster_coro_delete_self_reference(void* vc);
extern "C" void foster_write_barrier_with_obj_generic(void* ptr, void* obj, void** slot);

int foster__runtime__main__wrapper(int argc, char** argv) {
  bool tru = opaquely_i32(0) == 0;

  foster::runtime::initialize(argc, argv, (void*) &tru);
  foster__main();

  if (!tru) {
    // kung-fu grip to prevent LTO from being too mean.
    printf("%p\n", &foster_write_barrier_with_obj_generic);
  }

  return foster::runtime::cleanup();
}

} // extern "C"


namespace foster {
std::string humanize_s(double val, const char* unit) {
  char buf[64] = { 0 };
  foster__humanize_s_ptr(val, &buf[0], unit);
  return std::string(&buf[0]);
}

std::string fmt_secs(double secs) {
  char buf[64] = { 0 };
  foster_fmttime_secs_ptr(secs, &buf[0]);
  return std::string(&buf[0]);
}
} // namepsace foster


