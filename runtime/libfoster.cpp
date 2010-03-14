// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <cstdio>
#include <inttypes.h>
#include <cstdlib>

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

extern "C" {
void* memalloc(int64_t sz) { return malloc(sz); }
  
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



