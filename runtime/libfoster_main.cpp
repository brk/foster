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

#include "libfoster.h"
#include "foster_gc.h"

// This goes in the unnamed namespace so that the symbol won't be
// exported in the bitcode file, which could interfere with llc.
namespace {
foster::runtime::gc::StackEntry *llvm_gc_root_chain;
}

namespace foster {
namespace runtime {
namespace gc {

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta)) {
  for (StackEntry *R = llvm_gc_root_chain; R; R = R->Next) {
    unsigned i = 0;

    // For roots [0, NumMeta), the metadata pointer is in the FrameMap.
    for (unsigned e = R->Map->NumMeta; i != e; ++i)
      Visitor(&R->Roots[i], R->Map->Meta[i]);

    // For roots [NumMeta, NumRoots), the metadata pointer is null.
    for (unsigned e = R->Map->NumRoots; i != e; ++i) {
      Visitor(&R->Roots[i], NULL);
    }
  }
}

} } }

int main(int argc, char** argv) {
  foster::runtime::initialize();
  int rv = foster__main();
  foster::runtime::cleanup();
  return rv;
}

