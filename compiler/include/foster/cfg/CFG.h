// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_CFG_H
#define FOSTER_CFG_H

#include "parse/FosterAST.h"

#include <vector>
#include <utility>
#include <sstream>

struct CodegenPass;

namespace llvm {
  struct BasicBlock;
  struct Function;
  struct Value;
}

namespace foster {

class CFG {
public:
  CFG(const std::string& suggestedName,
      ExprAST* parentAST,
        FnAST* parentFn)
      : suggestedName(suggestedName),
        parentAST(parentAST),
        ourBB(NULL),
        lastNonVoidValue(NULL),
        terminator(getDefaultTerminator()) {
    parentFn->cfgs.push_back(this);
  }

  void append(ExprAST* expr);

  llvm::BasicBlock* codegen(CodegenPass*, llvm::Function* currentFn);

private:
  std::string suggestedName;
  ExprAST* parentAST;
  llvm::BasicBlock* ourBB;
  llvm::Value* lastNonVoidValue;

public:
  typedef std::pair<ExprAST*, CFG*> Edge;
  struct Terminator {
    // Makes graph iteration easy, but codegen hard.
    std::vector<Edge> edges;
    CFG*              parent;

    size_t getNumSuccessors() { return this ? edges.size() : 0; }
    CFG*  getParent() { return parent; }
    CFG*  getSuccessor(size_t i) { return edges[i].second; }
    ExprAST* getEdgeCond(size_t i) const { return edges[i].first; }

    virtual void codegen(CodegenPass* p) = 0;
  };

  static Terminator* getDefaultTerminator();

  std::string getBlockName() const { return suggestedName; }

  void addPredecessor(CFG* cfg);
  void setTerminator(Terminator* newterminator);
  void branchTo(CFG* next);
  void branchCond(ExprAST* cond, CFG* condTrue, CFG* condFalse);
  Terminator* getTerminator();
private:
  // Makes codegen easy, but graph iteration hard
  Terminator* terminator;

  std::vector<ExprAST*> exprs;
  std::vector<CFG*> predecessors;
};

} // namespace foster

#endif
