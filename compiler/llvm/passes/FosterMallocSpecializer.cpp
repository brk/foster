// Copyright (c) 2012 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#define DEBUG_TYPE "foster-specialize-malloc"

#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/ConstantFolding.h"

using namespace llvm;

STATISTIC(NumSpecialized, "Number of allocations specialized");

namespace {

class SpecializeAllocations : public BasicBlockPass {
  Constant *memalloc;
  Constant *memalloc_16;
  bool ready;
public:
  static char ID;
  explicit SpecializeAllocations() : BasicBlockPass(ID),
        memalloc(NULL), memalloc_16(NULL), ready(false) {}

  const char* getPassName() const { return "SpecializeAllocations"; }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesCFG();

    // TODO should add more preserved transforms here.
    AU.addPreserved<UnifyFunctionExitNodes>();
    AU.addPreservedID(LowerSwitchID);
    AU.addPreservedID(LowerInvokePassID);
  }

  bool doInitialization(Module &M);

  virtual bool doInitialization(Function &F) {
    return doInitialization(*F.getParent());
  }

  bool runOnBasicBlock(BasicBlock &BB);
};

char SpecializeAllocations::ID = 0;

} // unnnamed namespace

namespace llvm {
  void initializeSpecializeAllocationsPass(llvm::PassRegistry&);
}

INITIALIZE_PASS(SpecializeAllocations, "foster-malloc-specializer",
                "Call size-specific allocators when possible.",
                false, false);

namespace foster {

Pass* createMemallocSpecializerPass() { return new SpecializeAllocations(); }

} // namespace foster

bool SpecializeAllocations::doInitialization(Module &M) {
  memalloc    = M.getFunction("memalloc_cell");
  memalloc_16 = M.getFunction("memalloc_cell_16");
  ready = memalloc && memalloc_16;
  return true;
}

// runOnBasicBlock - This method does the actual work of converting
// instructions over, assuming that the pass has already been initialized.
//
bool SpecializeAllocations::runOnBasicBlock(BasicBlock &BB) {
  if (!BB.getParent()->hasGC()) return false;
  if (!ready) return false;

  bool Changed = false;
  assert(memalloc && memalloc_16 && "Pass not initialized!");

  BasicBlock::InstListType &BBIL = BB.getInstList();
  const DataLayout& TD = BB.getParent()->getParent()->getDataLayout();

  // Can't use range loop because we modify I in the loop...
  for (BasicBlock::iterator I = BB.begin(), E = BB.end(); I != E; ++I) {
    if (llvm::CallInst* call = llvm::dyn_cast<CallInst>(I)) {

      llvm::Function* F = call->getCalledFunction();

      // The memalloc might be bitcasted
      ConstantExpr* cc = dyn_cast<ConstantExpr>(call->getCalledValue());
      if (cc && cc->isCast()) {
        F = llvm::dyn_cast<Function>(cc->getOperand(0));
      }

      if (F == memalloc) {
        ConstantExpr* ac = dyn_cast<ConstantExpr>(call->getArgOperand(0));
        if (ac && ac->isCast()) {
          GlobalVariable* gv = dyn_cast<GlobalVariable>(ac->getOperand(0));
          ConstantStruct* cs = dyn_cast<ConstantStruct>(gv->getInitializer());
          ConstantExpr* sze = dyn_cast<ConstantExpr>(cs->getOperand(0));
          Constant* szc = ConstantFoldConstantExpression(sze, TD);
          if (szc && !llvm::isa<ConstantInt>(szc)) {
            szc = ConstantFoldConstantExpression(dyn_cast<ConstantExpr>(szc), TD);
          }
          if (!szc) {
            llvm::errs() << "FosterMallocSpecializer: Unable to evaluate allocated size!\n";
            exit(1);
          }
          ConstantInt* sz = dyn_cast<ConstantInt>(szc);
          if (!sz) {
            llvm::errs() << "FosterMallocSpecializer: Unable to evaluate allocated size to integer!\n";
            llvm::errs() << (*sze) << "\n";
            llvm::errs() << "was constant-folded by LLVM to:\n";
            llvm::errs() << (*szc) << "\n";
              exit(1);
          }

          // OK, we've computed the size of the allocation.
          // Let's see if we can specialize it...
          if (sz->getSExtValue() == 16) {
            // Replace call to memalloc with call to memalloc_16.
            Constant* mem16 = ConstantExpr::getBitCast(memalloc_16,
                                                        call->getCalledValue()->getType());
            CallInst* newcall = CallInst::Create(mem16, ac, "mem16_", &*I);
            call->replaceAllUsesWith(newcall);
            I = --BBIL.erase(I); // remove & delete the old memalloc call.
            ++NumSpecialized;
            Changed = true;
          }
        } else {
          if (ac && !ac->isCast()) {
            errs() << "FosterMallocSpecializer wasn't expecting "
                    << "direct call of (non-bit-casted) memalloc!";
          } else {
            errs() << "FosterMallocSpecializer wasn't able to find the called function! "
                    << call;
          }
          exit(1);
        }
      }
    }
  }

  return Changed;
}


