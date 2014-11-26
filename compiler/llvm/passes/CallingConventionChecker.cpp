// Copyright (c) 2012 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CallSite.h"

#include "base/GenericGraph.h"

#include <set>
#include <map>

using namespace llvm;

// Makes sure that call sites for calls to known functions don't
// use the wrong calling convention.

namespace {

struct CallingConventionChecker : public BasicBlockPass {
  Constant *memalloc;
  Constant *memalloc_16;
public:
  static char ID;
  explicit CallingConventionChecker() : BasicBlockPass(ID),
        memalloc(NULL), memalloc_16(NULL) {}

  const char* getPassName() const { return "SpecializeAllocations"; }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }

  bool doInitialization(Module &M);

  virtual bool doInitialization(Function &F) {
    return doInitialization(*F.getParent());
  }

  bool runOnBasicBlock(BasicBlock &BB);
};

char CallingConventionChecker::ID = 0;

} // unnamed namespace

namespace llvm {
  void initializeCallingConventionCheckerPass(llvm::PassRegistry&);
}

INITIALIZE_PASS(CallingConventionChecker, "foster-calling-convention-checker",
                "Check that known calls use the right calling convention",
                false, false);

namespace foster {

Pass* createCallingConventionCheckerPass() { return new CallingConventionChecker(); }

} // namespace foster


bool CallingConventionChecker::doInitialization(Module &M) {
  return true;
}

bool CallingConventionChecker::runOnBasicBlock(BasicBlock &BB) {
  if (!BB.getParent()->hasGC()) return false;
  bool Changed = false;
  bool sawSuspiciousCalls = false;

  for (BasicBlock::iterator I : BB) {
    if (llvm::CallInst* call = llvm::dyn_cast<CallInst>(I)) {
      llvm::Function* F = call->getCalledFunction();
      if (F) {
        llvm::CallingConv::ID fn_cc   =    F->getCallingConv();
        llvm::CallingConv::ID call_cc = call->getCallingConv();
        if (fn_cc != call_cc) {
          errs() << "***** CallingConventionChecker saw mismatched calling convention for call to " << F->getName() << "\n";
          sawSuspiciousCalls = true;
        }
      }
    }
  }

  if (sawSuspiciousCalls) exit(1);

  return Changed;
}
