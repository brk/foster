// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/PassManager.h"
#include "llvm/Transforms/Scalar.h"

#include "base/LLVMUtils.h"

#include "passes/FosterPasses.h"

namespace foster {

void runCleanupPasses(llvm::Module& mod) {
  llvm::FunctionPassManager fpasses(&mod);
  // Note that LLCodegen generates code which requires CFG simplification to
  // run to avoid keeping stale GC root temporaries.
  //    (^^^ is from late 2011 but I don't think it is true as of late 2013?)
  fpasses.add(llvm::createCFGSimplificationPass());
  // TODO: tailduplicate?
  foster::runFunctionPassesOverModule(fpasses, &mod);

  llvm::PassManager passes;
  passes.add(foster::createGCMallocFinderPass());
  passes.add(llvm::createDeadInstEliminationPass());
  passes.run(mod);
}

void runWarningPasses(llvm::Module& mod) {
  llvm::FunctionPassManager fpasses(&mod);
  fpasses.add(foster::createCallingConventionCheckerPass());
  fpasses.add(foster::createEscapingAllocaFinderPass());
  fpasses.add(foster::createGCRootSafetyCheckerPass());
  foster::runFunctionPassesOverModule(fpasses, &mod);
}

}
