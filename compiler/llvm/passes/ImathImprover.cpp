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

// Simple peephole optimizer for lowered ocde involving calls to
// the arbitrary-precision math library.
//
// Performs constant-folding and (eventually) API specialization.
// Examples of API specialization would include:
//
//   * Replacing _mul(%x, %x, %out) with _sqr(%x, %out)
//
//   * Replacing _mul(%mpvar, %mpconst, %out)
//          with _mul_value(%mpvar, word %constword, %out)


namespace {
struct ImathImprover : public BasicBlockPass {
  static char ID;
  ImathImprover() : BasicBlockPass(ID), builder(getGlobalContext()) {}

  llvm::IRBuilder<> builder;

  bool isCallTo(CallInst* call, const char* funcName) {
    if (!call) return false;
    Function* f = call->getCalledFunction();
    return f && f->hasName() && f->getNameStr() == funcName;
  }

  Value* getUseOf_Calling(Value* v, const char* funcName) {
    for (value_use_iterator<User> it = v->use_begin(); it != v->use_end(); ++it) {
      Value* u = *it;
      if (isCallTo(dyn_cast<CallInst>(u), funcName)) return u;
    }
    return NULL;
  }

  void scheduleForRemoval(Instruction* v, foster::GenericGraph<Instruction*>& g) {
    foster::GenericGraph<Instruction*>::NodePtr vnode = g.addNode(v);
    for (value_use_iterator<User> it = v->use_begin(); it != v->use_end(); ++it) {
      Instruction* u = dyn_cast<Instruction>(*it);
      g.addDirectedEdge(g.addNode(u), vnode, NULL);
    }
  }

  Value* getAppropriateOperation(Constant* c1, Constant* c2, const std::string& name) {
    Value* rv = StringSwitch<Value*>(name)
      .Case("mp_int_mul", builder.CreateMul(c1, c2))
      .Case("mp_int_add", builder.CreateAdd(c1, c2))
      .Default(NULL);
    ASSERT(rv) << "Don't know what operation to substitute for " << name;
    return rv;
  }

  virtual bool runOnBasicBlock(BasicBlock& BB) {
    std::set<CallInst*> mp_int_allocated;
    std::map<Value*, Constant*> small_mp_ints;

    Function* mp_int_init_value = NULL;

    // We store a graph of instructions to remove,
    // so that we can perform removals in topological sorted order,
    // by having uses point to defs.
    foster::GenericGraph<Instruction*> pendingRemovals;

    BasicBlock::InstListType& insns = BB.getInstList();
    for (BasicBlock::iterator it = insns.begin(),
                              e = insns.end(); it != e; ++it) {
      CallInst* call = dyn_cast<CallInst>(it);
      if (!call) continue;

      if (isCallTo(call, "mp_int_alloc")) {
        mp_int_allocated.insert(call);
      }

      else if (isCallTo(call, "mp_int_init_value")) {
        mp_int_init_value = call->getCalledFunction();

        unsigned int_arg = 0;
        unsigned val_arg = 1; // second arg, from 0
        Constant* c = cast<Constant>(call->getArgOperand(val_arg));
        small_mp_ints[call->getArgOperand(int_arg)] = c;
      }


      else if (isCallTo(call, "mp_int_mul")
            || isCallTo(call, "mp_int_add")) {
        Constant* c1 = small_mp_ints[call->getArgOperand(0)];
        Constant* c2 = small_mp_ints[call->getArgOperand(1)];
        std::string mp_operation = call->getCalledFunction()->getNameStr();

        if ((!c1) && (!c2)) {
          // TODO: convert _mul to _sqr here
          continue;
        }

        if (c1 && c2) {
          // If both args are constant values, replace with folded constant.

          // Have code like
          // %0 = call %mp_int @mp_int_alloc()
          // %1 = call i32 @mp_int_init_value(%mp_int %0, i32 5)
          // %2 = call %mp_int @mp_int_alloc()
          // %3 = call i32 @mp_int_init_value(%mp_int %2, i32 5)
          // %4 = call %mp_int @mp_int_alloc()
          // %5 = call i32 @mp_int_init(%mp_int %4)
          // %6 = call i32 @mp_int_mul(%mp_int %0, %mp_int %2, %mp_int %4)

          // Want to end up with just
          // %4 = call %mp_int @mp_int_alloc()
          // %7 = call i32 @mp_int_init_value(%mp_int %4, i32 25)

          Value* v4 = call->getArgOperand(2);
          // We must manually erase %0, %1, %2, %3, and %5
          // %0 and %2 are the call args
          Value* v0 = call->getArgOperand(0);
          Value* v2 = call->getArgOperand(1);
          // %1 and %3 are uses of %0 and %2 which are calls to mp_int_init_value.
          Value* v1 = getUseOf_Calling(v0, "mp_int_init_value");
          Value* v3 = getUseOf_Calling(v2, "mp_int_init_value");

          // %5 is the use of arg3 which is a call to mp_int_init
          Value* v5 = getUseOf_Calling(v4, "mp_int_init");

          // Replace %6 with, e.g
          // %7 = call i32 @mp_int_init_value(%mp_int %4, i32 25)
          builder.SetInsertPoint(&BB, it);
          Value* folded = getAppropriateOperation(c1, c2, mp_operation);
          Value* newcall = builder.CreateCall2(mp_int_init_value, v4, folded);
          call->replaceAllUsesWith(newcall);

          // Ensure that further intstructions know we've created a constant.
          small_mp_ints[v4] = cast<Constant>(folded);

          scheduleForRemoval(call, pendingRemovals);
          scheduleForRemoval(dyn_cast<Instruction>(v5), pendingRemovals);
          scheduleForRemoval(dyn_cast<Instruction>(v3), pendingRemovals);
          scheduleForRemoval(dyn_cast<Instruction>(v2), pendingRemovals);
          scheduleForRemoval(dyn_cast<Instruction>(v1), pendingRemovals);
          scheduleForRemoval(dyn_cast<Instruction>(v0), pendingRemovals);
        } else if (c1) {
        // If one arg is constant, use the _value variant.

        } else if (c2) {

        }
      }
    }

    // Now that we've identified all the redundant instructions, remove them.
    std::vector<foster::GenericGraph<Instruction*>::NodePtr> topo
      = pendingRemovals.getTopologicalSort();
    for (unsigned i = 0; i < topo.size(); ++i) {
      Instruction* inst = topo[i]->getValue();
      insns.erase(inst);
    }

    return false;
  }
};

char ImathImprover::ID = 0;

} // unnamed namespace

namespace llvm {
  void initializeImathImproverPass(llvm::PassRegistry&);
}

INITIALIZE_PASS(ImathImprover, "foster-imath-improver",
                "Peephole optimization of imath API calls",
                false, false);

namespace foster {

Pass* createImathImproverPass() { return new ImathImprover(); }

}
