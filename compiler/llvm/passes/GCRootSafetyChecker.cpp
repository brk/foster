// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/LLVMContext.h"
#include "llvm/Instructions.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Support/CallSite.h"

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
    //ImmutableCallSite cs(i);
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
    BasicBlock::iterator IP = F.getEntryBlock().begin();
    while (IP != F.getEntryBlock().end()
        && llvm::isa<llvm::AllocaInst>(IP)) {
      if (isGCRoot(IP)) {
        gcroots.insert(IP);
      }
      ++IP;
    }

    // Note each load from a gc root
    ValueSet                             gcroot_loads;
    std::map<llvm::Value*, llvm::Value*> gcroot_load_uses; // loaded val -> load

    for (std::set<llvm::Value*>::iterator it = gcroots.begin(); it != gcroots.end(); ++it) {
      llvm::Value* gcroot = *it;
      for (llvm::Value::use_iterator uit = gcroot->use_begin();
                                     uit != gcroot->use_end();
                                     ++uit) {
        llvm::User* use = *uit;
        if (llvm::isa<LoadInst>(use)) {
          gcroot_loads.insert(use);
          for (llvm::Value::use_iterator uit2 = use->use_begin();
                                         uit2 != use->use_end();
                                       ++uit2) {
            gcroot_load_uses[*uit2] = use;
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

    for (Function::iterator bb = F.begin(); bb != F.end(); ++bb) {
      ValueValueMap& tainted_loads = bb_tainted_loads[bb];
      ValueSet untainted_loads;
      union_of_predecessors(bb, tainted_loads, bb_tainted_loads);
      for (BasicBlock::iterator i = bb->begin(); i != bb->end(); ++i) {
        if (llvm::isa<CallInst>(i) || llvm::isa<InvokeInst>(i)) {
          if (callSiteMayGC(i)) {
            for (ValueSet::iterator utit = untainted_loads.begin();
                                    utit != untainted_loads.end(); ++utit) {
              tainted_loads[*utit] = i;
            }
            untainted_loads.clear();
          }
        } else if (llvm::isa<LoadInst>(i) && gcroot_loads.count(i) == 1) {
          untainted_loads.insert(i);
        } else if (llvm::Value* gcroot_load = gcroot_load_uses[i]) {
          if (llvm::Value* cause_of_gc = tainted_loads[gcroot_load]) {
            problems.push_back(StaleLoadInfo(F.getName(),
                               gcroot_load, i, cause_of_gc));
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

    if (!problems.empty()) exit(1);

    checkUsageOfPhis(F);

    return false;
  }

  void checkUsageOfPhis(Function& F) {
    for (Function::iterator bb = F.begin(); bb != F.end(); ++bb) {
      for (BasicBlock::iterator IP = bb->begin(); IP != bb->end(); ++IP) {
        if (! llvm::isa<llvm::PHINode>(IP)) { break; }
        // Non-pointers don't need to worry about GC staleness.
        if (! IP->getType()->isPointerTy()) { continue; }
        // A value with no uses is of, um, no use.
        if (  IP->use_begin() == IP->use_end()) { continue; }

        if (! isStoreToStackSlotOrRet(IP->use_back())) {
          llvm::errs() << "******** invalid use of phi node"
                       << " in function " << F.getName()
                       << "\n\tThis phi:   " << *IP
                       << "\n\tIs misused: " << *(IP->use_back());
          exit(1);
        }

        Value::use_iterator IPe = IP->use_begin(); IPe++;
        if (IPe != IP->use_end()) {
          llvm::errs() << "******** too many uses of phi node"
                       << " in function " << F.getName()
                       << "\n\tThis phi:   " << *IP;
          exit(1);
        }
      }
    }
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

INITIALIZE_PASS(GCRootSafetyChecker, "foster-escaping-alloca-finder",
                "Incomplete and unsound identification of escaping allocas",
                false, false);

namespace foster {

Pass* createGCRootSafetyCheckerPass() { return new GCRootSafetyChecker(); }

}
