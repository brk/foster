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

#include "base/GenericGraph.h"

#include <set>
#include <map>

using namespace llvm;

// If any alloca S or a bitcast of S is written to a stack slot,
// the stack slot becomes tainted.
//
// If a load from a tainted slot S1 is written to a stack slot S2,
// then S2 becomes tainted.
//
// If a load from a tainted slot, or bitcast thereof, is the
// return value of a function, then the function may have an
// escaping alloca.

namespace {
struct EscapingAllocaFinder : public FunctionPass {
  static char ID;
  EscapingAllocaFinder() : FunctionPass(ID) {}

  virtual bool runOnFunction(Function& F) {
    std::set<llvm::Value*> allocas;

    // Collect allocas
    BasicBlock::iterator IP = F.getEntryBlock().begin();
    while (IP != F.getEntryBlock().end()
        && llvm::isa<llvm::AllocaInst>(IP)) {
      allocas.insert(IP);
      ++IP;
    }

    // Calculate taint
    std::set<llvm::Value*> taintedSlots;
    for (std::set<llvm::Value*>::const_iterator ait = allocas.begin();
                                                ait != allocas.end();
                                                ++ait) {
      llvm::Value* alloca = *ait;
      for (llvm::Value::use_iterator uit = alloca->use_begin();
                                     uit != alloca->use_end();
                                     ++uit) {
        llvm::User* use = *uit;
        if (llvm::isa<StoreInst>(use)) {
          llvm::Value* v = use->getOperand(0)->stripPointerCasts();
          llvm::Value* dest = use->getOperand(1);
          if (llvm::isa<LoadInst>(v)) {
            v = llvm::dyn_cast<LoadInst>(v)->getOperand(0);
            if (taintedSlots.count(v) > 0) {
              taintedSlots.insert(dest);
              break;
            }
          } else {
            if (allocas.count(v) + taintedSlots.count(v) > 0) {
              taintedSlots.insert(dest);
              break;
            }
          }
        }
      }
    }

    // If any escaping terminator returns a tainted value, complain!
    bool wasTainted = false;
    for (Function::iterator BBit = F.begin(); BBit != F.end(); ++BBit) {
      TerminatorInst *ti = (*BBit).getTerminator();

      // Branches and invokes do not escape, only unwind and return do.
      if (isa<UnwindInst>(ti) || isa<ReturnInst>(ti)) {
        if (ti->getNumOperands() == 0) continue;

        llvm::Value* retval = ti->getOperand(0)->stripPointerCasts();
        llvm::Value* loaded = NULL;
        if (llvm::isa<LoadInst>(retval)) {
          loaded = llvm::dyn_cast<LoadInst>(retval)->getOperand(0);
        }
        if (allocas.count(retval) > 0) {
          llvm::errs() << "************** returning alloca in " << F.getName() << "!\n"
                << "\t" << *(ti) << "\n";
          wasTainted = true;
        } else if (taintedSlots.count(retval)
                 + taintedSlots.count(loaded) > 0) {
          llvm::errs() << "************** returning possibly escaping alloca in " << F.getName() << "!\n"
                << "\t" << *(ti) << "\n";
          wasTainted = true;
        }
      }
    }

    if (wasTainted) {
      exit(1);
    }

    return false;
  }
};

char EscapingAllocaFinder::ID = 0;

} // unnamed namespace

namespace llvm {
  void initializeEscapingAllocaFinderPass(llvm::PassRegistry&);
}

INITIALIZE_PASS(EscapingAllocaFinder, "foster-escaping-alloca-finder",
                "Incomplete and unsound identification of escaping allocas",
                false, false);

namespace foster {

Pass* createEscapingAllocaFinderPass() { return new EscapingAllocaFinder(); }

}
