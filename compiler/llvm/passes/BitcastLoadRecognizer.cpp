// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#define DEBUG_TYPE "foster-bitcast-recognizer"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/ADT/Statistic.h"

#include "base/GenericGraph.h"

#include <set>
#include <map>
#include <vector>

using namespace llvm;
using namespace llvm::PatternMatch;
using std::vector;

// Inspired by the example seen in John Regehr's blog post
//      http://blog.regehr.org/archives/959
// which also happens to be useful in accelerating a variety
// of bit-bashing code, such as siphash.

STATISTIC(NumSpecialized, "Number of bitcast loads specialized");

// Simple peephole optimizer to turn code like
//
//   %arrayidx1 = getelementptr inbounds i16* %buf, i32 1        ; #uses = 1	; i16*
//   %arrayidx4 = getelementptr inbounds i16* %buf, i32 2        ; #uses = 1	; i16*
//   %arrayidx8 = getelementptr inbounds i16* %buf, i32 3        ; #uses = 1	; i16*
//   %0 = load i16* %buf, align 2                                ; #uses = 1	; i16
//   %1 = load i16* %arrayidx1, align 2                          ; #uses = 1	; i16
//   %2 = load i16* %arrayidx4, align 2                          ; #uses = 1	; i16
//   %3 = load i16* %arrayidx8, align 2                          ; #uses = 1	; i16
//   %conv = zext i16 %0 to i64                                  ; #uses = 1	; i64
//   %conv2 = zext i16 %1 to i64                                 ; #uses = 1	; i64
//   %conv5 = zext i16 %2 to i64                                 ; #uses = 1	; i64
//   %conv9 = zext i16 %3 to i64                                 ; #uses = 1	; i64
//   %shl3 = shl nuw nsw i64 %conv2, 16                          ; #uses = 1	; i64
//   %shl6 = shl nuw nsw i64 %conv5, 32                          ; #uses = 1	; i64
//   %shl10 = shl nuw i64 %conv9, 48                             ; #uses = 1	; i64
//   %or = or i64 %shl3, %conv                                   ; #uses = 1	; i64
//   %or7 = or i64 %or, %shl6                                    ; #uses = 1	; i64
//   %or11 = or i64 %or7, %shl10                                 ; #uses = 1	; i64
//
// into
//
//   %buf.cast = bitcast i16* %buf to i64*              ; #uses = 1	; i64*
//   %or11 = load i64* %buf.cast, align 2 ; #uses = 1	; i64
//
// which corresponds to transforming
//      (((T)buf[0]) << (0 * sizeof(buf[0])))
//    | (((T)buf[1]) << (1 * sizeof(buf[0])))
//    | (((T)buf[2]) << (2 * sizeof(buf[0])))
//    | (((T)buf[3]) << (3 * sizeof(buf[0])))
// into
//      ((T*)buf)[0]
//
// This is valid on a little-endian architecture... but what isn't, these days?

// An index: base[index_base + index_offset] << shift_offset;
struct Idx {
  Value* base;
  Value* origin;
  int    gep_zeros;
  int    base_size;
  Value* index_base;
  int    index_offset;
  int    shift_offset;
};

bool by_index_offset(Idx* a, Idx* b) {
  return a->index_offset < b->index_offset;
}

struct BitcastLoadRecognizer : public BasicBlockPass {
  static char ID;
  BitcastLoadRecognizer() : BasicBlockPass(ID) {}

  const char* getPassName() const { return "BitcastLoadRecognizer"; }

  int sz(Type* t) {
    if (t->isIntegerTy()) {
           return t->getIntegerBitWidth();
    } else return 0;
  }

  // i is either a constant, a variable, or the sum of a var and a constant.
  void matchGEP_Index(Value* i, Value*& out_base, int& out_offset) {
    ConstantInt* c1;
    //errs() << "matchGEP_Index called on " << *i << "\n";
    if (match(i, m_Add(m_Value(out_base), m_ConstantInt(c1)))) {
        out_offset = c1->getZExtValue(); // truncation, but that's OK.
    } else {
      if (match(i, m_ConstantInt(c1))) {
        out_offset = c1->getZExtValue(); // truncation, but that's OK.
        out_base = ci32(0);
      } else {
        out_base = i;
        out_offset = 0;
      }
    }
  }

  Value* tryGetGEP(Value* v, Value*& out_base, int& out_offset, int& gep_zeros) {
    if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(v)) {
      if (gep->getNumIndices() > 2)    return NULL;
      User::op_iterator idx = gep->idx_begin();
      if (gep->getNumIndices() == 2) {
        if (ConstantInt* c = dyn_cast<ConstantInt>(idx)) {
          if (!c->isZero()) return NULL;
        } else return NULL;
        ++gep_zeros;
        idx++;
      }
      matchGEP_Index(*idx, out_base, out_offset);
      return gep->getPointerOperand();
    } else return NULL;
  }

  ConstantInt* ci32(int o) { return ConstantInt::get(Type::getInt32Ty(llvm::getGlobalContext()), o); }

  bool spec(Idx* r0, Type* newLoadType, Instruction* exp) {
    IRBuilder<> b(getGlobalContext());
    b.SetInsertPoint(exp);

    std::vector<llvm::Value*> offsets;
    for (int i = 0; i < r0->gep_zeros; ++i) { offsets.push_back(ci32(0)); }
    offsets.push_back(b.CreateAdd(r0->index_base, ci32(r0->index_offset)));
    Value*    bufptr  = b.CreateGEP(r0->base, llvm::makeArrayRef(offsets), "buf.off");
    Value*    bufcast = b.CreateBitCast(bufptr, PointerType::get(newLoadType, 0),
                                              "buf.cast");
    LoadInst* bufload = b.CreateLoad(bufcast, "buf.load");

    if (bufload->getType() != exp->getType()) {
      Value* zext     = new ZExtInst(bufload, exp->getType(), "buf.zext", exp);
      exp->replaceAllUsesWith(zext);
    } else {
      exp->replaceAllUsesWith(bufload);
    }

    // TODO: propagate alignment from the loads (conservatively)
    //bufload->setAlignment(l0->getAlignment());

    NumSpecialized++;
    return true;
  }

  Idx* newIdx(Value* v, int shiftdelta) {
     Idx* rv = new Idx();
     rv-> base = NULL;
     rv-> base_size    = 0;
     rv-> gep_zeros    = 0;
     rv-> index_base   = NULL;
     rv-> index_offset = 0;
     rv-> shift_offset = shiftdelta;
     rv-> origin = v;
     return rv;
  }

  void buildIdxBase(Value* v, Idx* idx) {
    idx->index_offset = -1;
    Value* b = tryGetGEP(v, idx->index_base, idx->index_offset, idx->gep_zeros);
    if (b && idx->index_offset != -1) {
      //errs() << "base is b: " << *b << "\n";
      idx->base         = b;
    } else {
      //errs() << "base is v: " << *v << "\n";
      idx->base         = v;
      idx->index_offset = 0;
    }
  }

  void buildIdx(Value* v, Idx* idx) {
    Value *x = NULL;
    ConstantInt *c = NULL;

    if (match(v,  m_ZExt(m_Value(x)))) {
      //errs() << "explorign child of zext: " << *x << "\n";
      return buildIdx(x, idx);
    }

    if (match(v,  m_Shl(m_Value(x),
                        m_ConstantInt(c)))) {
      idx->shift_offset += c->getZExtValue();
      //errs() << "explorign child of shl: " << *x << "\n";
      return buildIdx(x, idx);
    }

    if (LoadInst* ld = dyn_cast<LoadInst>(v)) {
      idx->base_size = sz(ld->getType());
      return buildIdxBase(ld->getPointerOperand(), idx);
    }
  }

  Value* stripZExt(Value* v) { Value* r;
     if (match(v, m_ZExt(m_Value(r)))) return r;
     return v;

  }
  void matchOrSubtree(Value* exp, Value*& a, int& da) {
    ConstantInt* c = NULL;
    exp = stripZExt(exp);
       match(exp, m_Shl(m_Value(a),  m_ConstantInt(c)))
    || match(exp,       m_Value(a));
    if (c) {
      da = c->getZExtValue();
    }
  }

  bool matchOrSubtrees(Value* exp, Value*& a, Value*& b, int& da, int& db) {
    if (match(stripZExt(exp), (m_Or(m_Value(a), m_Value(b))))) {
      matchOrSubtree(a, a, da);
      matchOrSubtree(b, b, db);
      return true;
    }
    return false;
  }

  // Invariant: exp is the child of an or-expression.
  bool collectOrResults(Value* exp, int shiftdelta, vector<Idx*>& res, vector<Value*>& ors) {
    Value* a, * b; int da = 0; int db = 0;
    if (matchOrSubtrees(exp, a, b, da, db)) {
      ors.push_back(stripZExt(exp));
      return collectOrResults(a, shiftdelta + da, res, ors)
          && collectOrResults(b, shiftdelta + db, res, ors);
    } else {
      //errs() << "collectOrResults of " << *exp << "\n";
      Idx* r = newIdx(exp, shiftdelta);
      buildIdx(exp, r);
      res.push_back(r);
      return r != NULL;
    }
  }

  bool allHaveSameNonNullBase(const vector<Idx*>& res) {
    Value* base = res[0]->base;
    if (!base) return false;
    for (int i = 1; i < res.size(); ++i) {
      if (res[i]->base != base) return false;
    }
    return true;
  }

  bool allHaveSameIndexBase(const vector<Idx*>& res) {
    for (int i = 1; i < res.size(); ++i) {
      if (res[0]->index_base != res[i]->index_base) return false;
      if (res[0]->gep_zeros  != res[i]->gep_zeros ) return false;
    }
    return true;
  }

  bool haveIncreasingLoads(const vector<Idx*>& res) {
    Idx* b = res[0];

    // The requirement that shift offset == 0 lets us avoid re-shifting
    // the loaded result. We assume the underlying hardware can support
    // unaligned reads, so index_offset need not be zero.
    if (b->shift_offset != 0) return false;
    for (int i = 1; i < res.size(); ++i) {
      if (res[i]->index_offset -
          res[0]->index_offset != b->shift_offset + i) return false;
      if (res[i]->shift_offset != b->base_size    * i) return false;
    }
    // TODO if we see shifts in the opposite order, we can generate
    // a load followed by a bswap?
    return true;
  }

  virtual bool runOnBasicBlock(BasicBlock& BB) {
    std::set<Value*>  willBeDead;

    // Iterate over the instructions in reverse order so that we see
    // "big" subtrees before "small" ones.
    BasicBlock::InstListType& insns = BB.getInstList();
    for (BasicBlock::InstListType::reverse_iterator it = insns.rbegin(),
                                      en = insns.rend(); it != en; ++it) {
      Instruction* exp = &(*it);
      BinaryOperator* bo = dyn_cast<BinaryOperator>(exp);

      // Quickly skip any instructions that aren't an "or",
      // or that are doomed to everlasting oblivion.
      if ( (!bo) || bo->getOpcode() != Instruction::Or
                 || willBeDead.count(bo) > 0 ) {
         continue;
      }

      vector<Idx*> indexes;
      vector<Value*> ors;
      if (collectOrResults(bo, 0, indexes, ors)) {
        if (indexes.size() <= 1) continue;

        sort(indexes.begin(), indexes.end(), by_index_offset);

        if (0) {
          errs() << "<<<<<<<<<<<<<\n";
          errs() << "root insn: " << *(bo) << " has " << bo->getNumUses() << " uses\n";
          errs() << "root insn will be dead? " << willBeDead.count(bo) << "\n";

          for (int i = 0; i < indexes.size(); ++i) {
            if (!indexes[i]) errs() << "<null>\n";
            else {
              errs() << "origin: " << *(indexes[0]->origin) << "\n\n";
              if (indexes[i]->base) {
                errs() << "base: " << *(indexes[i]->base);
              } else {
                errs() << "no base;";
              }
              errs() << " base size: "
                     <<   indexes[i]->base_size
                     << " index offset: "
                     <<   indexes[i]->index_offset
                     << " shift offset: "
                     <<   indexes[i]->shift_offset << "\n";
              errs() << " index base: " << *(indexes[i]->index_base) << "\n";
            }
          }
          errs() << ">>>>>>>>>>>>>\n";
        }

        if (!allHaveSameNonNullBase(indexes)) {
          //llvm::errs() << "skipping because they don't all have the same base\n";
          continue;
        }

        if (!allHaveSameIndexBase(indexes)) {
          //llvm::errs() << "skipping because they don't all have the same index base\n";
          continue;
        }

        if (!haveIncreasingLoads(indexes)) {
          //llvm::errs() << "skipping because they don't have increasing loads\n";
          continue;
        }

        //llvm::errs() << "specializing " << indexes.size() << " loads into one\n";

        spec(indexes[0],
             Type::getIntNTy(getGlobalContext(),
                                  indexes[0]->base_size * indexes.size()), bo);

        for (int i = 0; i < ors.size(); ++i) {
          //errs() << "marking to-be-dead " << *ors[i] << "\n";
          willBeDead.insert(ors[i]);
        }
      }
    }
    return false;
  }
};

char BitcastLoadRecognizer::ID = 0;

namespace llvm {
  void initializeBitcastLoadRecognizerPass(llvm::PassRegistry&);
}

INITIALIZE_PASS(BitcastLoadRecognizer, "foster-bitcast-recognizer",
                "Peephole optimization of suboptimal bitcasting pattern",
                false, false);

namespace foster {

Pass* createBitcastLoadRecognizerPass() { return new BitcastLoadRecognizer(); }

}
