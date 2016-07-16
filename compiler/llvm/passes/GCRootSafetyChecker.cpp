// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Intrinsics.h"
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

// Checks that LLVM IR does not contain instances of the following
// subtle anti-pattern:
// slot = alloca i32* (marked as gcroot)
// ptr  = load slot
// call force_gc_for_debugging_purposes (or any other function that can trigger gc)
// use ptr
//
//
// Or this one:
// call @llvm.lifetime.start(x)
// ...
// (no intervening lifetime.end())
// ...
// call @llvm.lifetime.start(x)

namespace {

struct StaleLoadInfo {
  std::string funcName;
  llvm::Value* load;
  llvm::Value* use;
  llvm::Value* cause;
  StaleLoadInfo(std::string funcName,
                llvm::Value* load,
                llvm::Value* use,
                llvm::Value* cause) :
    funcName(funcName), load(load), use(use), cause(cause) {}
};

struct GCRootSafetyChecker : public FunctionPass {
  static char ID;
  GCRootSafetyChecker() : FunctionPass(ID) {}

  const char* getPassName() const { return "GCRootSafetyChecker"; }

  bool callSiteMayGC(llvm::Instruction* i) {
    if (i->getMetadata("willnotgc")) {
      return false;
    }
    return true;
  }

  //  * Iterate over each basic block, noting which values
  //    result from loads of gc root slots.
  //  * At every potential GC point, mark every value seen so far as tainted.
  //  * Complain when a tainted value is used.

  typedef std::set<llvm::Value*> ValueSet;
  typedef std::map<llvm::Value*, llvm::Value*> ValueValueMap;

  bool isGCRoot(const Instruction* v) {
    return v && v->getMetadata("fostergcroot") != NULL;
  }

  bool isStoreToStackSlotOrRet(const Instruction* v) {
    const llvm::StoreInst* si = llvm::dyn_cast<llvm::StoreInst>(v);
    return (si != NULL && llvm::isa<llvm::AllocaInst>(si->getPointerOperand()))
        || (si == NULL && llvm::isa<llvm::ReturnInst>(v));
  }

  virtual bool runOnFunction(Function& F) {
    if (!F.hasGC()) return false;
    if (!llvm::StringRef(F.getGC()).startswith("fostergc")) return false;

    ValueSet gcroots;

    // Collect gc roots
    for (BasicBlock::iterator IP : F.getEntryBlock()) {
      if (!llvm::isa<llvm::AllocaInst>(IP)) break;
      if (isGCRoot(IP)) {
        gcroots.insert(IP);
      }
    }

    // Note each load from a gc root
    ValueSet gcroot_loads;
    // loaded val -> load
    std::map<llvm::Value*, ValueSet> gcroot_load_uses;

    for (llvm::Value* gcroot : gcroots) {
      for (llvm::Value::use_iterator uit = gcroot->use_begin();
                                     uit != gcroot->use_end();
                                     ++uit) {
        llvm::Value* use = (*uit);
        if (llvm::isa<LoadInst>(use)) {
          gcroot_loads.insert(use);
          for (llvm::Value::use_iterator uit2 = use->use_begin();
                                         uit2 != use->use_end();
                                       ++uit2) {
            gcroot_load_uses[*uit2].insert(use);
          }
        }
      }
    }

    // Calculate taint:
    //  * If we see a load from a gc root, check if it is tainted
    //  * If we see a call that might gc, taint loaded values.
    // We accumulate the effects of basic blocks, to avoid overly conservative
    // results from simply iterating over the instructions.
    std::map<llvm::BasicBlock*, ValueValueMap> bb_tainted_loads;
    std::vector<StaleLoadInfo> problems;
    std::map<const llvm::Value*, const llvm::Value*> lifetime_started;

    for (Function::iterator bb : F) {
      ValueValueMap& tainted_loads = bb_tainted_loads[bb];
      ValueSet untainted_loads;
      union_of_predecessors(bb, tainted_loads, bb_tainted_loads);
      // Iterate through each instruction in each basic block.
      for (BasicBlock::iterator i : *bb) {
        if (llvm::isa<CallInst>(i) || llvm::isa<InvokeInst>(i)) {
          // {{{ lifetime intrinsic handling
          ImmutableCallSite cs(i);
          const llvm::Function* f = cs.getCalledFunction();
          if (f && f->getIntrinsicID() == llvm::Intrinsic::lifetime_start) {
            const llvm::Value* arg = cs.getArgument(1)->stripPointerCasts();
            const llvm::Value* orig = lifetime_started[arg];
            if (!orig) {
              lifetime_started[arg] = i;
            } else {
              llvm::errs() << "******** repeated call to llvm.lifetime.start"
                     << " likely to cause problems in function " << F.getName()
                     << "\n\tFirst:      " << *orig
                     << "\n\tSecond:     " << *i << "\n";
            }
          } else if (f && f->getIntrinsicID() == llvm::Intrinsic::lifetime_end) {
            // we don't consider multiple ends to be a problem, because
            // this is ok::
            //          A:
            //            lifetime begin
            //            condbr B C
            //          B:
            //            lifetime end
            //          C:
            //            lifetime end
            const llvm::Value* arg = cs.getArgument(1)->stripPointerCasts();
            lifetime_started.erase(arg);
          } else
          // }}}
          // {{{ gc root taint handling
                 if (f && f->getIntrinsicID() != llvm::Intrinsic::not_intrinsic) {
            // call site won't gc...
          } else if (callSiteMayGC(i)) {
            // Taint every untainted load.
            for (auto load : untainted_loads) {
              tainted_loads[load] = i;
            }
            untainted_loads.clear();
          }
          // }}}
        } else if (llvm::isa<LoadInst>(i) && gcroot_loads.count(i) == 1) {
          // Loads from gcroots are untainted until we hit the next gc point.
          untainted_loads.insert(i);
        } else {
          // Other instruction -- maybe it's using a stale load?
          ValueSet& load_uses = gcroot_load_uses[i];
          for (auto gcroot_load : load_uses) {
            if (llvm::Value* cause_of_gc = tainted_loads[gcroot_load]) {
              problems.push_back(StaleLoadInfo(F.getName(),
                                 gcroot_load, i, cause_of_gc));
            }
          }
        }
      } // end basic block iteration
    } // end function iteration

    for (size_t i = 0; i < problems.size(); ++i) {
      StaleLoadInfo& si = problems[i];
      llvm::errs() << "******** indirect use of stale load"
                   << " after potential GC in function " << si.funcName
                   << "\n\tThis value is stale: " << *si.load
                   << "\n\tWhen used here:      " << *si.use
                   << "\n\tDue to potential GC: " << *si.cause << "\n";
    }

    //if (!problems.empty()) exit(1);

    return false;
  }

  void union_of_predecessors(BasicBlock* BB, ValueValueMap& results,
                             std::map<llvm::BasicBlock*, ValueValueMap>& bb_tainted_loads)
  {
    for (pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; ++PI) {
      ValueValueMap& vs = bb_tainted_loads[*PI];
      results.insert(vs.begin(), vs.end());
    }
  }
};

char GCRootSafetyChecker::ID = 0;

} // unnamed namespace

namespace llvm {
  void initializeGCRootSafetyCheckerPass(llvm::PassRegistry&);
}

INITIALIZE_PASS(GCRootSafetyChecker, "foster-gc-root-safety-checker",
                "Incomplete and unsound identification of dodgy gc root usage",
                false, false);

namespace foster {

Pass* createGCRootSafetyCheckerPass() { return new GCRootSafetyChecker(); }

}
