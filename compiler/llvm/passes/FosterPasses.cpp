// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Scalar.h"

#include "base/LLVMUtils.h"

#include "passes/FosterPasses.h"

namespace foster {

void runCleanupPasses(llvm::Module& mod) {
  llvm::legacy::FunctionPassManager fpasses(&mod);
  
  fpasses.add(llvm::createCFGSimplificationPass());
  foster::runFunctionPassesOverModule(fpasses, &mod);

  llvm::legacy::PassManager passes;
  passes.add(llvm::createDeadInstEliminationPass());
  passes.add(foster::createGCBarrierOptimizerPass());
  passes.run(mod);
}

void runWarningPasses(llvm::Module& mod) {
  llvm::legacy::FunctionPassManager fpasses(&mod);
  fpasses.add(foster::createCallingConventionCheckerPass());
  fpasses.add(foster::createEscapingAllocaFinderPass());
  fpasses.add(foster::createGCRootSafetyCheckerPass());
  foster::runFunctionPassesOverModule(fpasses, &mod);
}

}
