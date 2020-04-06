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
#include "base/LLVMUtils.h"

#include <set>
#include <map>

using namespace llvm;

// Makes sure that call sites for calls to known functions don't
// use the wrong calling convention.

namespace {

struct CallingConventionChecker : public FunctionPass {
  Constant *memalloc;
  Constant *memalloc_16;
public:
  static char ID;
  explicit CallingConventionChecker() : FunctionPass(ID),
        memalloc(NULL), memalloc_16(NULL) {}

  llvm::StringRef getPassName() const { return "CallingConventionChecker"; }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }

  bool doInitialization(Module &M);

  virtual bool doInitialization(Function &F) {
    return doInitialization(*F.getParent());
  }

  virtual bool runOnFunction(Function& F);
  void runOnBasicBlock(BasicBlock&, bool&);
};

char CallingConventionChecker::ID = 0;

} // unnamed namespace

namespace llvm {
  void initializeCallingConventionCheckerPass(llvm::PassRegistry&);
}

INITIALIZE_PASS(CallingConventionChecker, "foster-calling-convention-checker",
                "Check that known calls use the right calling convention",
                true, false);

namespace foster {

Pass* createCallingConventionCheckerPass() { return new CallingConventionChecker(); }

} // namespace foster


bool CallingConventionChecker::doInitialization(Module &M) {
  return true;
}

bool CallingConventionChecker::runOnFunction(Function& F) {
  if (!isFosterFunction(F)) return false;

  bool Changed = false;
  for (BasicBlock& BB : F) {
    runOnBasicBlock(BB, Changed);
  }

  return Changed;
}


void CallingConventionChecker::runOnBasicBlock(BasicBlock &BB, bool& Changed) {
  bool sawSuspiciousCalls = false;

  for (Instruction& Iref : BB) {
    Instruction* I = &Iref;
    if (llvm::CallInst* call = llvm::dyn_cast<CallInst>(I)) {
      llvm::Function* F = call->getCalledFunction();
      if (F) {
        llvm::CallingConv::ID fn_cc   =    F->getCallingConv();
        llvm::CallingConv::ID call_cc = call->getCallingConv();
        if (fn_cc != call_cc) {
          errs() << "***** CallingConventionChecker saw mismatched calling convention for call to "
                 << F->getName() << "\n"
                 << "The function's cc is " << fn_cc << " but the call's was " << call_cc << "\n";
          sawSuspiciousCalls = true;
        }
      }
    }
  }

  if (sawSuspiciousCalls) exit(1);
}
