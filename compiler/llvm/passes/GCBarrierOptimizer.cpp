// Copyright (c) 2018 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/CallSite.h"

#include "base/GenericGraph.h"

#include <set>
#include <map>

using namespace llvm;

// When we have a barrier to write a pointer P to slot S,
// we can elide the barrier if P points into the subheap that contains S.
//
// One common instance of this pattern is
// * Allocate X
// * Allocate Y
// * Write Y into X
// (with no intervening calls to subheap_activate()).
//
// Note that this optimization is *not* valid for a generational write barrier!

namespace llvm {
  void initializeGCBarrierOptimizerPass(llvm::PassRegistry&);
}

namespace {

struct GCBarrierOptimizer : public CallGraphSCCPass {
  static char ID;
  explicit GCBarrierOptimizer() : CallGraphSCCPass(ID) {
    llvm::initializeGCBarrierOptimizerPass(*PassRegistry::getPassRegistry());
  }

  llvm::StringRef getPassName() const { return "GCBarrierOptimizer"; }

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesCFG();
    CallGraphSCCPass::getAnalysisUsage(AU);
  }

  //  * Iterate over each basic block, maintaining a list of objects allocated
  //    in the current subheap. Function parameters are treated conservatively.
  //  * When calling a function that might activate a new subheap, clear the list.
  //  * When a barrier writes two objects in the list, elide it.

  typedef std::set<llvm::Value*> ValueSet;
  typedef std::map<llvm::Value*, llvm::Value*> ValueValueMap;

  std::set<llvm::Function*> functionsThatMightChangeSubheaps;
  std::set<llvm::Function*> allocatorFunctions;

  bool mightChangeSubheaps(Function* F) const {
    return (!F) || functionsThatMightChangeSubheaps.count(F) == 1;
  }

  virtual bool doInitialization(CallGraph& CG) {
    Function* f = CG.getModule().getFunction("foster_subheap_activate");
    functionsThatMightChangeSubheaps.insert(f);

    Function* a = CG.getModule().getFunction("memalloc_cell");
    llvm::outs() << "GC Barrier optimizer starting with " << *f << " and " << *a << "\n";
    allocatorFunctions.insert(a);
    allocatorFunctions.insert(CG.getModule().getFunction("memalloc_cell_16"));
    allocatorFunctions.insert(CG.getModule().getFunction("memalloc_cell_32"));
    allocatorFunctions.insert(CG.getModule().getFunction("memalloc_cell_48"));
    allocatorFunctions.insert(CG.getModule().getFunction("memalloc_array"));
    return false;
  }

  virtual bool runOnSCC(CallGraphSCC& SCC) {

    // If any function in the SCC might activate a new subheap, they all must be marked.
    bool mightActivateNewSubheap = false;
    for (CallGraphNode* cgn : SCC) {
      for (unsigned i = 0; i < cgn->size(); ++i) {
        llvm::Function* callee = cgn[i].getFunction();
        if (mightChangeSubheaps(callee)) {
          mightActivateNewSubheap = true;
        }
      }
    }

    if (mightActivateNewSubheap) {
      for (CallGraphNode* cgn : SCC) {
        functionsThatMightChangeSubheaps.insert(cgn->getFunction());
      }
    }

    ValueSet objectsInCurrentSubheap;
    ValueSet rootSlotsHoldingCurrentSubheapObjects;

    // Now that we have an accounting of which functions might cause subheap activation,
    // go through each function and elide unnecessary write barriers.
    for (CallGraphNode* cgn : SCC) {
      Function* F = cgn->getFunction();

      if (!F) continue;
      if (!F->hasGC()) continue;
      if (!llvm::StringRef(F->getGC()).startswith("fostergc")) continue;

      int numReturnInstructionsTotal = 0;
      int numReturnsOfFreshAllocations = 0;

      int numTotalWriteBarriers = 0;
      int numElidableWriteBarriers = 0;

      std::vector<Instruction*> markedForDeath;

      for (BasicBlock& bb : *F) {
        for (Instruction& I : bb) {
          Value* bare = I.stripPointerCasts();

          if (ReturnInst* ri = dyn_cast<ReturnInst>(bare)) {
            ++numReturnInstructionsTotal;
            Value* rv = ri->getReturnValue();
            if (rv) {
              if (CallInst* rvc = dyn_cast<CallInst>(rv->stripPointerCasts())) {
                if (allocatorFunctions.count(rvc->getCalledFunction()) == 1) {
                  ++numReturnsOfFreshAllocations;
                }
              } else if (isa<Constant>(rv)) {
                  // Constants include GlobalValues, null pointers, and undef,
                  // none of which would lead to triggering write barriers.
                  ++numReturnsOfFreshAllocations;
              }
            }
          }

          if (StoreInst* si = dyn_cast<StoreInst>(bare)) {
            Value* slot = si->getPointerOperand()->stripPointerCasts();
            if (isa<AllocaInst>(slot)) {
              if (objectsInCurrentSubheap.count(si->getValueOperand()->stripPointerCasts())) {
                rootSlotsHoldingCurrentSubheapObjects.insert(slot);
              }
            }
          }

          if (CallInst* ci = dyn_cast<CallInst>(bare)) {
            Function* calleeOrNull = ci->getCalledFunction();
            if (mightChangeSubheaps(calleeOrNull)) {
              objectsInCurrentSubheap.clear();
              rootSlotsHoldingCurrentSubheapObjects.clear();
            }

            if (allocatorFunctions.count(calleeOrNull) == 1) {
              objectsInCurrentSubheap.insert(ci);
            }

            // Intrinsics, such as write barriers, are call instructions.
            if (IntrinsicInst* ii = dyn_cast<IntrinsicInst>(ci)) {
              if (ii->getIntrinsicID() == llvm::Intrinsic::gcwrite) {
                ++numTotalWriteBarriers;

                Value* ptr  = ii->getArgOperand(0)->stripPointerCasts();
                Value* slot = ii->getArgOperand(2)->stripPointerCasts();
                if (auto gep = dyn_cast<GetElementPtrInst>(slot)) {
                  slot = gep->getPointerOperand()->stripPointerCasts();
                }

                bool ptrInCurrentSubheap = objectsInCurrentSubheap.count(ptr) == 1
                                            || isa<Constant>(ptr);
                bool slotInCurrentSubheap = objectsInCurrentSubheap.count(slot) == 1
                                            || isa<Constant>(slot);
                if (auto load = dyn_cast<LoadInst>(ptr)) {
                  ptrInCurrentSubheap = rootSlotsHoldingCurrentSubheapObjects.count(
                                            load->getPointerOperand()->stripPointerCasts()) == 1;
                }
                if (auto load = dyn_cast<LoadInst>(slot)) {
                  slotInCurrentSubheap = rootSlotsHoldingCurrentSubheapObjects.count(
                                            load->getPointerOperand()->stripPointerCasts()) == 1;
                }

                if (ptrInCurrentSubheap && slotInCurrentSubheap) {
                  ++numElidableWriteBarriers;
                  llvm::outs() << "specializing gcwrite of " << ptr->getName() << " to " << slot->getName() << "\n";
                  auto si = new StoreInst(ii->getArgOperand(0), ii->getArgOperand(2), ii);
                  ii->replaceAllUsesWith(si);
                  markedForDeath.push_back(ii);
                } else {
                  llvm::outs() << "cannot specialize gcwrite of " << ptr->getName() << " to " << slot->getName() << ";"
                        << "ptr? " << ptrInCurrentSubheap << "; slot? " << slotInCurrentSubheap << "\n";
                }
              }
            }
          }
        }
      }

      for (auto inst : markedForDeath) {
        inst->eraseFromParent();
      }

      if (numTotalWriteBarriers > 0) {
        llvm::outs() << "numTotalWriteBarriers: " << numTotalWriteBarriers << "\n";
      }
      if (numElidableWriteBarriers > 0) {
        llvm::outs() << "numElidableWriteBarriers: " << numElidableWriteBarriers << "\n";
      }

      if ( (numReturnInstructionsTotal > 0)
            && (numReturnsOfFreshAllocations == numReturnInstructionsTotal) ) {
        allocatorFunctions.insert(F);

        llvm::outs() << "marking " << F->getName() << " as an allocating function\n";
      } else {
        llvm::outs() << "        " << F->getName() << " not'n allocating function"
                << "(" << numReturnInstructionsTotal << " vs " << numReturnsOfFreshAllocations << ")\n";
      }
    }

    return false;
  }
};

char GCBarrierOptimizer::ID = 0;

} // unnamed namespace

/*
INITIALIZE_PASS(GCBarrierOptimizer, "foster-gc-barrier-optimizer",
                "Flow-based optimization of GC write barriers",
                false, false)
*/

INITIALIZE_PASS_BEGIN(GCBarrierOptimizer, "foster-gc-barrier-optimizer", "Flow-based optimization of GC write barriers", /*cfgonly=*/true, /*analysis=*/false)
INITIALIZE_PASS_DEPENDENCY(CallGraphWrapperPass)
INITIALIZE_PASS_END(GCBarrierOptimizer, "foster-gc-barrier-optimizer", "Flow-based optimization of GC write barriers", /*cfgonly=*/true, /*analysis=*/false)


namespace foster {

Pass* createGCBarrierOptimizerPass() { return new GCBarrierOptimizer(); }

}
