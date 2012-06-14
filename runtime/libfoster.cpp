// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include "libfoster.h"
#include "foster_gc.h"
#include "libfoster_gc_roots.h"

#include "_generated_/imath.h"
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

std::vector<coro_context> coro_initial_contexts;
int    foster_argc;
char** foster_argv;

extern "C"
struct foster_bytes {
   int64_t cap;
   int8_t bytes[0];
};

// primitive defined by the compiler itself
extern "C" void* foster_emit_string_of_cstring(const char*, int32_t);

namespace foster {
namespace runtime {

void initialize(int argc, char** argv) {
  cpuid_info info;
  cpuid_introspect(info);

  int cachesmall = cpuid_small_cache_size(info);
  int cachelarge = cpuid_large_cache_size(info);

  // TODO Initialize one default coro context per thread.
  coro_initial_contexts.push_back(coro_context());
  coro_create(&coro_initial_contexts[0], 0, 0, 0, 0);

  current_coro = NULL;

  gc::initialize();

  foster_argc = argc;
  foster_argv = argv;
}

int cleanup() {
  return gc::cleanup();
}

template <int N, typename Int>
int fprint_b2(FILE* f, Int x) {
  char* buf = new char[N+1];
  buf[N] = '\0';
  for (int i = 0; i < N; ++i) {
    buf[(N-1) - i] = (x & (1<<i)) ? '1' : '0';
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

void fprint_i32(FILE* f, int32_t x) {  fprintf(f, "%d\n", x); fflush(f); }
void fprint_i32x(FILE* f, int32_t x) { fprintf(f, "%X_16\n", x); }
void fprint_i32b(FILE* f, int32_t x) { fprint_b2<32>(f, x); }

void fprint_mp_int(FILE* f, mp_int m, int radix) {
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
  fprintf(f, "%s\n", buf);
  free(buf);
}

void fprint_bytes(FILE* f, foster_bytes* array, uint32_t n) {
  uint32_t c = array->cap;
  fprintf(f, "%.*s\n", (std::min)(n, c), &array->bytes[0]);
}

} } // namespace foster::runtime

using namespace foster::runtime;

extern "C" {

//////////////////////////////////////////////////////////////////

void foster__assert(bool ok, const char* msg) {
  if (!ok) {
    fprintf(stderr, "%s\n", msg);
    fflush(stderr);
    exit(1);
  }
}

void foster__boundscheck64(int64_t idx, int64_t len, const char* srclines) {
  if (idx < 0 || idx >= len) {
    fprintf(stderr, "bounds check failed: cannot index array of "
                    "length %" PRId64 " with value % " PRId64 "\n"
                    "%s", len, idx, srclines);
    fflush(stderr);
    exit(1);
  }
}

int force_gc_for_debugging_purposes() {
  gc::force_gc_for_debugging_purposes(); return 0;
}

void foster__mp_int(mp_int m) {  mp_small small;
  mp_result conv = mp_int_to_int(m, &small); }
void  print_int(mp_int m) { fprint_mp_int(stdout, m, 10); }
void expect_int(mp_int m) { fprint_mp_int(stderr, m, 10); }
void  print_intx(mp_int m) { fprint_mp_int(stdout, m, 16); }
void expect_intx(mp_int m) { fprint_mp_int(stderr, m, 16); }
void  print_intb(mp_int m) { fprint_mp_int(stdout, m, 2); }
void expect_intb(mp_int m) { fprint_mp_int(stderr, m, 2); }

void  print_i8(int8_t x) { fprint_i32(stdout, x); } // implicit conversion
void expect_i8(int8_t x) { fprint_i32(stderr, x); } // implicit conversion

void  print_i32(int32_t x) { fprint_i32(stdout, x); }
void expect_i32(int32_t x) { fprint_i32(stderr, x); }

void  print_i32x(int32_t x) { fprint_i32x(stdout, x); }
void expect_i32x(int32_t x) { fprint_i32x(stderr, x); }

void  print_i32b(int32_t x) { fprint_i32b(stdout, x); }
void expect_i32b(int32_t x) { fprint_i32b(stderr, x); }

int read_i32() { int32_t n; scanf(" %d", &n); return n; }

void  print_i64(int64_t x) { fprint_i64(stdout, x); }
void expect_i64(int64_t x) { fprint_i64(stderr, x); }
void expect_i64x(int64_t x) { fprint_i64x(stderr, x); }
void expect_i64b(int64_t x) { fprint_i64b(stderr, x); }

// C type "bool" becomes LLVM "i8 zeroext", not "i1"
void  print_i1(bool x) { fprintf(stdout, (x ? "true\n" : "false\n")); }
void expect_i1(bool x) { fprintf(stderr, (x ? "true\n" : "false\n")); }

// This is used by the compiler.
uint8_t foster_ctor_id_of(void* body) {
  return foster::runtime::ctor_id_of(body);
}

void print_addr(void* x) { fprintf(stdout, "addr: %p\n", x); }

void prim_print_bytes_stdout(foster_bytes* array, uint32_t n) {
  fprint_bytes(stdout, array, n);
}

void prim_print_bytes_stderr(foster_bytes* array, uint32_t n) {
  fprint_bytes(stderr, array, n);
}

void print_float_p9f64(double f) { return fprint_p9f64(stdout, f); }
void expect_float_p9f64(double f) { return fprint_p9f64(stderr, f); }

void* get_cmdline_arg_n(int32_t n) {
  if (n >= 0 && n < foster_argc) {
      const char* s = foster_argv[n];
      return foster_emit_string_of_cstring(s, strlen(s));
  } else {
      const char* s = "";
      return foster_emit_string_of_cstring(s, 0);
  }
}

extern int32_t opaquely_i32(int32_t n);

} // extern "C"

