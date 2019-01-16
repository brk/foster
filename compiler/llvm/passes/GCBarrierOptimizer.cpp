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
#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/Cloning.h"

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
//
//
// This is conceptually a CallGraphSCC pass, but on-demand function cloning
// makes it very awkward to write the pass under the assumptions/constraints
// of CallGraphSCC. Thus, we make it a ModulePass that simply computes the SCC
// before doing its work. The changes we make to the SCC are sufficiently restricted
// that we can get away without recomputing the call graph as we go along.

namespace llvm {
  void initializeGCBarrierOptimizerPass(llvm::PassRegistry&);
}

#define DEBUG_TYPE "foster-barrier-optimizer"

STATISTIC(NumBarriersElided, "Number of write barriers elided");
STATISTIC(NumBarriersPresent, "Number of write barriers present");
STATISTIC(NumCallsModified, "Number of calls redirected to cloned versions");

namespace {

struct GCBarrierOptimizer : public ModulePass {
  static char ID;
  explicit GCBarrierOptimizer() : ModulePass(ID) {
    llvm::initializeGCBarrierOptimizerPass(*PassRegistry::getPassRegistry());
  }

  llvm::StringRef getPassName() const { return "GCBarrierOptimizer"; }

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesCFG();
    AU.addRequired<CallGraphWrapperPass>();
    ModulePass::getAnalysisUsage(AU);
  }

  //  * Iterate over each basic block, maintaining a list of objects allocated
  //    in the current subheap. Function parameters are treated conservatively.
  //  * When calling a function that might activate a new subheap, clear the list.
  //  * When a barrier writes two objects in the list, elide it.

  typedef std::set<llvm::Value*> ValueSet;
  typedef std::map<llvm::Value*, llvm::Value*> ValueValueMap;

  std::set<llvm::Function*> functionsThatMightChangeSubheaps;
  std::set<llvm::Function*> functionsThatWillNotChangeSubheaps;
  std::set<llvm::Function*> allocatorFunctions;
  //std::map<Function*, std::pair<Function*, CallGraphNode*> > currSubheapClones;
  std::map<Function*, Function*> currSubheapClones;

  bool mightChangeSubheaps(Function* F) const {
    if (!F) return true;
    if (functionsThatWillNotChangeSubheaps.count(F) == 1) return false;
    if (allocatorFunctions.count(F) == 1) return false;
    return functionsThatMightChangeSubheaps.count(F) == 1;
  }

  virtual bool doInitialization(Module& M) {
    Function* f = M.getFunction("foster_subheap_activate");
    functionsThatMightChangeSubheaps.insert(f);

    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_ctor_id_of"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("memcpy_i8_to_at_from_len"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("printf"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("fprintf"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("fwrite"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("fflush"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("malloc"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("TextFragment"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster__assert"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster__logf64"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_coro_create"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster__boundscheck64"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_subheap_create_raw"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_subheap_create_small_raw"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_subheap_condemn_raw"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_subheap_collect"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_emit_string_of_cstring"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_get_cmdline_arg_n_raw"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("foster_fmttime_secs_raw"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("prim_print_bytes_stdout"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("prim_print_bytes_stderr"));
    functionsThatWillNotChangeSubheaps.insert(M.getFunction("print_newline"));
    if (auto F = M.getFunction("foster__record_closure_call")) {
      functionsThatWillNotChangeSubheaps.insert(F);
    }

    Function* a = M.getFunction("memalloc_cell");
    //llvm::outs() << "GC Barrier optimizer starting with " << *f << " and " << *a << "\n";
    allocatorFunctions.insert(a);
    allocatorFunctions.insert(M.getFunction("memalloc_cell_16"));
    allocatorFunctions.insert(M.getFunction("memalloc_cell_32"));
    allocatorFunctions.insert(M.getFunction("memalloc_cell_48"));
    allocatorFunctions.insert(M.getFunction("memalloc_array"));


    for (auto it = M.begin(); it != M.end(); ++it) {
      ValueToValueMapTy vmap;
      //Function* callee = const_cast<Function*>(*it);
      Function* callee = &*it;
      if (!callee || !callee->hasGC()
          || !llvm::StringRef(callee->getGC()).startswith("fostergc")
          || callee->getName().endswith(".subClone")) { continue; }
      //llvm::outs() << "Cloning " << callee->getName() << "\n";
      llvm::Function* cloned = llvm::CloneFunction(callee, vmap);
      cloned->setName(cloned->getName() + ".subClone");
      //currSubheapClones[callee] = std::make_pair(cloned, CG.getOrInsertFunction(cloned));
      //currSubheapClones[callee] = std::make_pair(cloned, new CallGraphNode(cloned));
      currSubheapClones[callee] = cloned;
    }

    return true;
  }

  virtual bool runOnModule(Module& M) {
    /*
    std::vector<CallGraphNode*> augmentedCGNs;
    for (CallGraphNode* cgn : SCC) { augmentedCGNs.push_back(cgn); }
    for (int i = 0, e = augmentedCGNs.size(); i < e; ++i) {
      auto p = currSubheapClones[ augmentedCGNs[i]->getFunction() ];
      augmentedCGNs.push_back(p.second);
    }
    SCC.initialize(augmentedCGNs);
    */

    CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    scc_iterator<CallGraph*> CGI = scc_begin(&CG);

    ValueSet objectsInCurrentSubheap;
    ValueSet rootSlotsHoldingCurrentSubheapObjects;

    while (!CGI.isAtEnd()) {
      CallGraphSCC SCC(CG, &CGI);
      SCC.initialize(*CGI);
      ++CGI;

      //llvm::outs() << "// Considering new CallGraphSCC..." << "\n";

      // If any function in the SCC might activate a new subheap, they all must be marked.
      bool mightActivateNewSubheap = false;
      for (CallGraphNode* cgn : SCC) {
        if (!cgn || !cgn->getFunction()) { continue; }
        if (functionsThatWillNotChangeSubheaps.count(cgn->getFunction()) == 1) {
          continue;
        }
        //cgn->dump();
        for (auto callRecordIter = cgn->begin(), end = cgn->end(); callRecordIter != end; ++callRecordIter) {
          auto callee = callRecordIter->second->getFunction();
          if (mightChangeSubheaps(callee)) {
            /*
            if (callee) {
              llvm::outs() << "Callee might activate new subheap: " << callee->getName() << "\n";
            } else {
              llvm::outs() << "Callee might activate new subheap: <unknown function>" << "\n";
              Value* call = callRecordIter->first;
              if (call) {
                llvm::outs() << "   call: " << *call << "\n";
              } else {
                llvm::outs() << "   call unknown" << "\n";
              }
            }
            */
            mightActivateNewSubheap = true;
          }
        }
      }

      if (mightActivateNewSubheap) {
        for (CallGraphNode* cgn : SCC) {
          if (!cgn) { continue; }
          Function* f = cgn->getFunction();
          //if (f) {
          //  llvm::outs() << "SCC/CGN node might activate new subheap: " << f->getName() << "\n";
          //}
          functionsThatMightChangeSubheaps.insert(f);
        }
      }

      // Now that we have an accounting of which functions might cause subheap activation,
      // go through each function and elide unnecessary write barriers.
      for (CallGraphNode* cgn : SCC) {
        if (!cgn) { continue; }
        Function* F = cgn->getFunction();

        if (!F) continue;
        if (!F->hasGC()) continue;
        if (!llvm::StringRef(F->getGC()).startswith("fostergc")) continue;

        processFunction(F, objectsInCurrentSubheap, rootSlotsHoldingCurrentSubheapObjects);

        auto clonedFunc = currSubheapClones[F];
        if (clonedFunc) {
          processFunction(clonedFunc, objectsInCurrentSubheap, rootSlotsHoldingCurrentSubheapObjects);
        }
      }

    }

    return false;
  }

  void processFunction(Function* F, ValueSet& objectsInCurrentSubheap,
                                    ValueSet& rootSlotsHoldingCurrentSubheapObjects) {

    int numReturnInstructionsTotal = 0;
    int numReturnsOfFreshAllocations = 0;

    int numTotalWriteBarriers = 0;
    int numElidableWriteBarriers = 0;

    bool isCloned = F->getName().endswith(".subClone");
    if (isCloned) {
      auto it = F->arg_begin();
      for (unsigned i = 0; i < F->arg_size(); ++i) {
        auto arg = &*it++;
        if (arg->getType()->isPointerTy()) {
          objectsInCurrentSubheap.insert(arg);
        }
      }
    }

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

          {
            auto cloneit = currSubheapClones.find(calleeOrNull);
            if (cloneit != currSubheapClones.end() && cloneit->second/*.second*/ != nullptr) {
              auto clonedFunc = cloneit->second;
              bool noArgsOutsideCurrentSubheap = true;
              bool hasArgsInsideCurrentSubheap = false;
              for (auto& arg : ci->arg_operands()) {
                auto val = arg->stripPointerCasts();
                bool isPointer = val->getType()->isPointerTy();
                if (!isPointer) { continue; }
                bool ptrInCurrentSubheap = objectsInCurrentSubheap.count(val) == 1
                                        || isa<Constant>(val);  
                if (ptrInCurrentSubheap) {
                  hasArgsInsideCurrentSubheap = true;
                } else {
                  noArgsOutsideCurrentSubheap = false;
                }
              }

              if (noArgsOutsideCurrentSubheap && hasArgsInsideCurrentSubheap) {
                ++NumCallsModified;
                //llvm::outs() << "recognized call of " << (calleeOrNull ? calleeOrNull->getName() : "<unknown>")
                //            << " as being passed only current-subheap args; " << clonedFunc
                //            << ";  isCloned? " << isCloned << "\n"
                //            << *ci << "\n";
                ci->setCalledFunction(clonedFunc);
                calleeOrNull = clonedFunc;
                //SCC.ReplaceNode(cgn, cloneit->second.second);
              }
            }
          }
          

          if (mightChangeSubheaps(calleeOrNull)) {
            //if (calleeOrNull != nullptr) {
            //  llvm::outs() << F->getName() << " clearing root list due to call of " << calleeOrNull->getName() << "\n";
            //}
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
                //llvm::outs() << "specializing gcwrite of " << ptr->getName() << " to " << slot->getName() << "\n";
                auto si = new StoreInst(ii->getArgOperand(0), ii->getArgOperand(2), ii);
                ii->replaceAllUsesWith(si);
                markedForDeath.push_back(ii);
                NumBarriersElided++;
              } else {
                NumBarriersPresent++;
                llvm::outs() << F->getName() << ": cannot specialize gcwrite of " << ptr->getName() << " to " << slot->getName() << ";"
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

/*
    if (numTotalWriteBarriers > 0) {
      llvm::outs() << "numTotalWriteBarriers: " << numTotalWriteBarriers << "\n";
    }
    if (numElidableWriteBarriers > 0) {
      llvm::outs() << "numElidableWriteBarriers: " << numElidableWriteBarriers << "\n";
    }
    */

    if ( (numReturnInstructionsTotal > 0)
          && (numReturnsOfFreshAllocations == numReturnInstructionsTotal) ) {
      allocatorFunctions.insert(F);
      //llvm::outs() << "marking " << F->getName() << " as an allocating function\n";
    } else {
      /*
      llvm::outs() << "        " << F->getName() << " not'n allocating function"
              << "(" << numReturnInstructionsTotal << " vs " << numReturnsOfFreshAllocations << ")\n";
              */
    }
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
