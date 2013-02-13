// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

// This goes in a separate source file from libfoster.cpp
// because having a main() function there interferes with
// fosterc's linking process.

////////////////////////////////////////////////////////////////

#include "libfoster.h"

// This symbol is hardcoded in fosterc (specifically, CodegenPass.cpp)
// as the replacement for any "main" function.
extern "C" int foster__runtime__main__wrapper(int argc, char** argv);
extern "C" int foster__main();

int main(int argc, char** argv) {
  return foster__runtime__main__wrapper(argc, argv);
  //foster::runtime::initialize(argc, argv);
  //foster__main();
  //return foster::runtime::cleanup();
}

// This lives here to prevent it from being inlined away when
// programs are optimized after being linked with libfoster.
extern "C" int32_t opaquely_i32(int32_t n) { return n; }
