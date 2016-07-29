// Copyright (c) 2013 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CallSite.h"
#include "llvm/ADT/StringSwitch.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"

#include "base/LLVMUtils.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;

namespace {
// This could/should be a LoopPass but I was unable to figure out
// how to run a loop pass without LLVM asserting due to uninitialized
// Loop Pass Manager... ugh!
struct TimerChecksInsertion : public FunctionPass {
  static char ID;
  TimerChecksInsertion() : FunctionPass(ID), builder(getGlobalContext()) {}

  const char* getPassName() const { return "TimerChecksInsertion"; }
  llvm::IRBuilder<> builder;

  virtual void getAnalysisUsage(AnalysisUsage& AU) const {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<ScalarEvolution>();

    AU.addPreserved<LoopInfoWrapperPass>();
    AU.addPreserved<ScalarEvolution>();
  }

  // If F is recursive, or makes calls to statically unknown functions,
  // we should insert a check at the entry.
  bool needsHeader(llvm::Function& F) {
    for (Function::iterator BB : F) {
      for (BasicBlock::iterator I : *BB) {
        if (llvm::CallInst* call = llvm::dyn_cast<CallInst>(I)) {
          llvm::Value* Vtgt = call->getCalledValue();
          if (!Vtgt) {
            //errs() << F.getName() << " needs header due to unknown target " << str(call);
            return true; // Call to unknown function.
          }
          if (llvm::dyn_cast<llvm::Function>(Vtgt->stripPointerCasts()) == &F) {
            //errs() << F.getName() << " needs header due to recursive call " << str(call);
            return true; // Recursive call.
          }
        }
      }
    }

    return false;
  }

  bool isKnownAndReasonable(unsigned trips) {
    return trips > 0 && trips < 255;
  }

  llvm::Function* needReschedF;
  llvm::Function* doReschedF;

  virtual bool doInitialization(Module& M) {
    needReschedF = M.getFunction("__foster_need_resched_threadlocal");
    doReschedF   = M.getFunction("__foster_do_resched");
    return false;
  }

  void insertCheckAt(Function* F, BasicBlock* bb, Instruction* here) {
      BasicBlock* newbb = bb->splitBasicBlock(here);
      newbb->setName("postcheck_");
      // newbb takes all the stuff after the phi nodes in bb
      // bb now has an unconditional branch to newbb; erase it
      bb->getTerminator()->eraseFromParent();

      builder.SetInsertPoint(bb);

      Value* needsResched = builder.CreateCall(needReschedF, None, "needsResched");
      BasicBlock* doReschedBB = BasicBlock::Create(getGlobalContext(), "doyield", F, newbb);
      builder.CreateCondBr(needsResched, doReschedBB, newbb);

      builder.SetInsertPoint(doReschedBB);
      builder.CreateCall(doReschedF);
      builder.CreateBr(newbb);
  }

  virtual bool runOnFunction(llvm::Function& F) {
    if (!isFosterFunction(F)) { return false; }

    bool modified = false;
    std::vector<Loop*> loops;

    LoopInfo& LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    for (auto loop : LI) {
      loops.push_back(loop);
    }

    ScalarEvolution& SE = getAnalysis<ScalarEvolution>();

    for (auto loop : loops) {
      // Don't insert checks in blocked/tiled inner loops.
      if (isKnownAndReasonable(SE.getSmallConstantTripCount(loop))) continue;
      BasicBlock* bb = loop->getHeader();
      insertCheckAt(&F, bb, bb->getFirstNonPHI());
    }

    modified = !loops.empty();

    /*
    Otherwise, if there are no loops, the function can't diverge (though it
    (perhaps) can block in native platform/library function calls, which
    cannot be safely pre-empted...
    */
    if (loops.empty() && needsHeader(F)) {
      BasicBlock* bb = &F.getEntryBlock();
      insertCheckAt(&F,  bb, bb->getTerminator());
      modified = true;
    }

    //outs() << "TimerChecksInsertion ran on function " << F.getName()
    //       << " with " << headers.size() << " headers; modified? "  << modified << "\n";

    return modified;
  }
};

char TimerChecksInsertion::ID = 0;

} // unnamed namespace

namespace llvm {
  void initializeTimerChecksInsertionPass(llvm::PassRegistry&);
}

INITIALIZE_PASS_BEGIN(TimerChecksInsertion, "foster-timer-checks",
                "Insertion of timer checks at loop headers",
                false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
//INITIALIZE_PASS_DEPENDENCY(LoopAnalysis)
INITIALIZE_PASS_END(TimerChecksInsertion, "foster-timer-checks",
                "Insertion of timer checks at loop headers",
                false, false)

namespace foster {

Pass* createTimerChecksInsertionPass() {
  return new TimerChecksInsertion();
}

}
