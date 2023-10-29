// Copyright (c) 2012 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#define DEBUG_TYPE "foster-specialize-malloc"

#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/ConstantFolding.h"

#include "base/LLVMUtils.h"

using namespace llvm;

STATISTIC(NumSpecialized, "Number of allocations specialized");

namespace {

class SpecializeAllocations : public PassInfoMixin<SpecializeAllocations> {
  llvm::Function *memalloc;
  llvm::Function *memalloc_16;
  llvm::Function *memalloc_32;
  llvm::Function *memalloc_48;
  bool ready;
public:
  explicit SpecializeAllocations() :
        memalloc(NULL), memalloc_16(NULL), memalloc_32(NULL), memalloc_48(NULL), ready(false) {}

  llvm::StringRef getPassName() const { return "SpecializeAllocations"; }

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
      doInitialization(M);
      bool anymod = false;
      for (auto &F : M) {
        anymod |= runOnFunction(F, M, AM);
      }

      return anymod ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesCFG();

    // TODO should add more preserved transforms here.
    AU.addPreserved<llvm::UnifyFunctionExitNodesLegacyPass>();
    AU.addPreservedID(LowerSwitchID);
    AU.addPreservedID(LowerInvokePassID);
  }

  bool doInitialization(Module &M);

  void runOnBasicBlock(BasicBlock&, bool&);
  bool runOnFunction(Function& F, Module &M, ModuleAnalysisManager &AM);
};

} // unnnamed namespace

namespace foster {

void addMemallocSpecializerPass(ModulePassManager &MPM) {
  MPM.addPass(SpecializeAllocations());
}

} // namespace foster

bool SpecializeAllocations::doInitialization(Module &M) {
  memalloc    = M.getFunction("memalloc_cell");
  memalloc_16 = M.getFunction("memalloc_cell_16");
  memalloc_32 = M.getFunction("memalloc_cell_32");
  memalloc_48 = M.getFunction("memalloc_cell_48");
  ready = memalloc && memalloc_16 && memalloc_32 && memalloc_48;
  return true;
}

llvm::FunctionCallee of(llvm::Function* fv) { return llvm::FunctionCallee(fv); }

BasicBlock::iterator eraseInstruction(BasicBlock& BB, BasicBlock::iterator I) {
  BasicBlock::iterator next = I; ++next;
  return BB.erase(I, next);
}

// runOnBasicBlock - This method does the actual work of converting
// instructions over, assuming that the pass has already been initialized.
//
void SpecializeAllocations::runOnBasicBlock(BasicBlock& BB, bool& Changed) {
  const DataLayout& TD = BB.getParent()->getParent()->getDataLayout();

  // Can't use range loop because we modify I in the loop...
  for (BasicBlock::iterator I = BB.begin(), E = BB.end(); I != E; ++I) {
    if (llvm::CallInst* call = llvm::dyn_cast<CallInst>(I)) {

      llvm::Function* F = call->getCalledFunction();

      // The memalloc might be bitcasted
      ConstantExpr* cc = dyn_cast<ConstantExpr>(call->getCalledOperand());
      if (cc && cc->isCast()) {
        F = llvm::dyn_cast<Function>(cc->getOperand(0));
      }

      if (F == memalloc) {
        Constant* ac = dyn_cast<Constant>(call->getArgOperand(0));
        if (ac) {
          GlobalVariable* gv = dyn_cast<GlobalVariable>(ac);
          assert(gv && "had Constant but no GlobalVariable??");
          ConstantStruct* cs = dyn_cast<ConstantStruct>(gv->getInitializer());
          ConstantInt* sz = dyn_cast<ConstantInt>(cs->getOperand(0));
          if (!sz) {
            llvm::errs() << "FosterMallocSpecializer: Unable to evaluate allocated size!\n";
            exit(1);
          }

          // OK, we've computed the size of the allocation.
          // Let's see if we can specialize it...
          if (sz->getSExtValue() == 16) {
            // Replace call to memalloc with call to memalloc_16.
            CallInst* newcall = CallInst::Create(of(memalloc_16), ac, "mem16_", &*I);
            call->replaceAllUsesWith(newcall);
            I = eraseInstruction(BB, I);
            ++NumSpecialized;
            Changed = true;
          } else if (sz->getSExtValue() == 32) {
            // Replace call to memalloc with call to memalloc_32.
            CallInst* newcall = CallInst::Create(of(memalloc_32), ac, "mem32_", &*I);
            call->replaceAllUsesWith(newcall);
            I = eraseInstruction(BB, I); // remove & delete the old memalloc call.
            ++NumSpecialized;
            Changed = true;
            
          } else if (sz->getSExtValue() == 48) {
            // Replace call to memalloc with call to memalloc_48.
            CallInst* newcall = CallInst::Create(of(memalloc_48), ac, "mem48_", &*I);
            call->replaceAllUsesWith(newcall);
            I = eraseInstruction(BB, I); // remove & delete the old memalloc call.
            ++NumSpecialized;
            Changed = true;
          } else {
            //llvm::errs() << "Saw memalloc but can't specialize size " << sz->getSExtValue() << "\n";
          }
        } else {
          errs() << "FosterMallocSpecializer wasn't able to find the called function! "
                  << "\n" << *call
                  << "\n";
          exit(1);
        }
      }
    }
  }
}

bool SpecializeAllocations::runOnFunction(Function& F, Module &M, ModuleAnalysisManager &AM) {
  if (!isFosterFunction(F)) return false;
  if (!ready) return false;
  
  assert(memalloc && memalloc_16 && "Pass not initialized!");

  bool Changed = false;
  for (BasicBlock& BB : F) {
    runOnBasicBlock(BB, Changed);
  }

  return Changed;
}


