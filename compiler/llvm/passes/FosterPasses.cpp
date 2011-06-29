// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/LLVMUtils.h"
#include "llvm/PassManager.h"

#include "passes/FosterPasses.h"

namespace foster {

void runCleanupPasses(llvm::Module& mod) {
  llvm::FunctionPassManager fpasses(&mod);
  fpasses.add(foster::createImathImproverPass());
  foster::runFunctionPassesOverModule(fpasses, &mod);

  llvm::PassManager passes;
  passes.add(foster::createGCMallocFinderPass());
  passes.run(mod);
}

void runWarningPasses(llvm::Module& mod) {
  llvm::FunctionPassManager fpasses(&mod);
  fpasses.add(foster::createEscapingAllocaFinderPass());
  foster::runFunctionPassesOverModule(fpasses, &mod);
}

}
