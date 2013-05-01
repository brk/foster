// Copyright (c) 2013 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Module.h"
#include "llvm/LLVMContext.h"
#include "llvm/Instructions.h"
#include "llvm/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringSwitch.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"

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
    AU.addRequired<LoopInfo>();
    AU.addPreserved<LoopInfo>();
  }

  llvm::Value* needReschedF;

  virtual bool doInitialization(Module& M) {
    needReschedF = M.getFunction("__foster_need_resched_threadlocal");
    return false;
  }

  virtual bool runOnFunction(llvm::Function& F) {
    if (!isFosterFunction(F)) { return false; }

    /*
    TODO: if F is recursive, or makes calls to statically unknown functions,
    we should insert a check at the entry.
    Otherwise, if there are no loops, the function can't diverge (though it
    (perhaps) can block in native platform/library function calls, which
    cannot be safely pre-empted...
    */

    std::vector<BasicBlock*> headers;

    LoopInfo& LI = getAnalysis<LoopInfo>();
    for (LoopInfo::iterator it = LI.begin(); it != LI.end(); ++it) {
      const Loop* loop = *it;
      headers.push_back(loop->getHeader());
    }

    for (int i = 0; i < headers.size(); ++i) {
      BasicBlock* bb = headers[i];
      BasicBlock* newbb = bb->splitBasicBlock(bb->getFirstNonPHI());
      newbb->setName("postcheck_");
      // newbb takes all the stuff after the phi nodes in bb
      // bb now has an unconditional branch to newbb; erase it
      bb->getTerminator()->eraseFromParent();

      builder.SetInsertPoint(bb);

      Value* needsResched = builder.CreateCall(needReschedF, "needsResched");
      BasicBlock* doReschedBB = BasicBlock::Create(getGlobalContext(), "doyield", &F, newbb);
      builder.CreateCondBr(needsResched, doReschedBB, newbb);

      builder.SetInsertPoint(doReschedBB);
      // TODO: insert call to foster coro yield (against (thread local?) 'runtime' coro)...
      builder.CreateBr(newbb);
    }

    outs() << "TimerChecksInsertion ran on function " << F.getName()
           << " with " << headers.size() << "headers" << "\n";

    return false;
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
INITIALIZE_PASS_DEPENDENCY(LoopInfo)
INITIALIZE_PASS_END(TimerChecksInsertion, "foster-timer-checks",
                "Insertion of timer checks at loop headers",
                false, false)

namespace foster {

Pass* createTimerChecksInsertionPass() {
  return new TimerChecksInsertion();
}

}
