// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/DCE.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

#include "base/LLVMUtils.h"

#include "passes/FosterPasses.h"

namespace foster {

void runModulePasses(llvm::Module& mod, llvm::ModulePassManager& MPM) {
  using namespace llvm;
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;

  PassBuilder PB;

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  MPM.run(mod, MAM);
}

void runCleanupPasses(llvm::Module& mod) {
  llvm::ModulePassManager MPM;

  llvm::FunctionPassManager FPM;
  FPM.addPass(llvm::DCEPass());
  FPM.addPass(llvm::SimplifyCFGPass());
  MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));

  runModulePasses(mod, MPM);
}

void runWarningPasses(llvm::Module& mod) {
  llvm::FunctionPassManager FPM;
  //FPM.addPass(foster::createCallingConventionCheckerPass());
  //FPM.addPass(foster::createEscapingAllocaFinderPass());

  llvm::ModulePassManager MPM;
  MPM.addPass(createModuleToFunctionPassAdaptor(std::move(FPM)));

  runModulePasses(mod, MPM);
}

}
