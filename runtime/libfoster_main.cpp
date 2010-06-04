// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

// This goes in a separate source file from libfoster.cpp
// because having a main() function there interferes with
// fosterc's linking process.

////////////////////////////////////////////////////////////////

// This symbol is hardcoded in fosterc (specifically, CodegenPass.cpp)
// as the replacement for any "main" function.
extern "C" int foster__main();

#include "foster_gc.h"

int main(int argc, char** argv) {
  foster::runtime::gc::initialize();
  int rv = foster__main();
  foster::runtime::gc::cleanup();
  return rv;
}

