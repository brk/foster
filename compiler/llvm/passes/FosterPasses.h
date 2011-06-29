// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef LLVM_FOSTER_PASSES_H
#define LLVM_FOSTER_PASSES_H

namespace llvm {
  class Module;
  class Pass;
}


namespace foster {

void runCleanupPasses(llvm::Module& mod);
void runWarningPasses(llvm::Module& mod);

llvm::Pass* createImathImproverPass();
llvm::Pass* createGCMallocFinderPass();
llvm::Pass* createEscapingAllocaFinderPass();

}

#endif // header guard

