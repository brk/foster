// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <cstdio>
#include <inttypes.h>
#include <cstdlib>

#include <vector>

#include <pthread.h>

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
// compile this file to bitcode (with llvm-gcc or, eventually, clang),
// and link the two bitcode files together with llvm-ld.
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

#ifndef PRId64
#define PRId64 "lld"
#endif

struct FosterClosurei32 {
  int32_t (*code)(void* env);
  void* env;
};

int fprint_i64(FILE* f, int64_t x) { return fprintf(f, "%" PRId64 "\n", x) - 1; }
int fprint_i32(FILE* f, int32_t x) { return fprintf(f, "%d\n", x) - 1; }
int fprint_i32x(FILE* f, int32_t x) { return fprintf(f, "%X_16\n", x) - 1; }
int fprint_i32b(FILE* f, int32_t x) {
  static char buf[33];
  buf[32] = '\0';
  for (int i = 0; i < 32; ++i) {
    buf[31 - i] = (x & (1<<i)) ? '1' : '0';
  }
  return fprintf(f, "%s_2\n", buf);
}

std::vector<pthread_t> threadinfo;

typedef void (*GenericCallback)();
typedef int32_t (*i32Callback)();

void* i32_callback_invoker(void* arg) {
  int32_t rv = ((i32Callback) arg)();
  return NULL;
}

extern "C" {
  // This interface is slightly awkward, with the extra indirection, because:
  // 1) pthreads wants a function that returns a void*,
  //    which foster doesn't yet do, and
  // 2) llvm-g++ lowers the closure struct type given above, so foster sees
  //    a function of two pointer parameters instead of one struct type param.
  //    Thus, in order to pass a closure struct to a C function, we must either:
  //      a) Special-case this function in the typecheck and codegen passes (ew!)
  //      b) Add a generalized automatic-unpacking pass
  //         that applies to all functions (ew!)
  //      c) Track the origin of functions and only automatically unpack structs
  //         if we're calling a C function, and the LLVM types only match with
  //         the unpacking applied. (ugh!)
  //
  // Thus, the easiest route is to (implicitly) require that closures
  // be converted to standalone trampolines before being passed in.
  //
  // TODO: The C wrapper may end up being necessary anyways, in order
  // to pass thread id information (as well as the env) back to the callback.
  // Need to decide if and how thread ids and such should be handled.
  //
int32_t thread_create_i32(i32Callback f) {
  int32_t id = threadinfo.size();
  threadinfo.push_back(pthread_t());
  return pthread_create(&threadinfo[id], NULL, i32_callback_invoker, (void*) f);
}

int32_t thread_waitall() {
  int nthreads = threadinfo.size();
  for (int i = 0; i < nthreads; ++i) {
    pthread_join(threadinfo[i], NULL);
  }
  threadinfo.clear();
  return nthreads;
}

int32_t c_invoke_closure_i32(FosterClosurei32 clo) { return clo.code(clo.env); }
//void c_invoke_closure_void(FosterClosureVoid clo) { clo.code(clo.env); }

void c_invoke_fnptr_void(void (*f)()) { f(); }
int32_t c_invoke_fnptr_i32(int32_t (*f)()) { return f(); }

// Interface to foster's memory allocator; see gc/foster_gc_allocate.cpp
void* memalloc(int64_t sz);

//////////////////////////////////////////////////////////////////

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
