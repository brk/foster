// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/Assert.h"
#include "parse/FosterAST.h"
#include "passes/CodegenPass.h"
#include "cfg/CFG.h"
#include "parse/FosterUtils.h"
#include "passes/PrettyPrintPass.h"

#include "llvm/Instructions.h"
#include "llvm/Support/raw_ostream.h"

#include "pystring/pystring.h"

using foster::EDiag;
using foster::show;

namespace foster {

struct RetTerminator : public CFG::Terminator {
  explicit RetTerminator() {}

  virtual void codegen(CodegenPass* p) {
    ASSERT(false) << "RetTerminator codegen not implemented";
  }
};

CFG::Terminator* CFG::getDefaultTerminator() {
  return new RetTerminator();
}

void CFG::append(ExprAST* ast) { exprs.push_back(ast); }

struct UnconditionalBranch : public CFG::Terminator {
  explicit UnconditionalBranch(CFG* target) {
    edges.push_back(CFG::Edge(NULL, target));
  }

  virtual void codegen(CodegenPass* p) {
    ASSERT(false) << "UnconditionalBranch codegen not implemented";
  }
};

struct ConditionalBranch : public CFG::Terminator {
  ExprAST* cond;
  explicit ConditionalBranch(ExprAST* cond,
                             CFG* whenTrue,
                             CFG* whenFalse)
  : cond(cond) {
    edges.push_back(CFG::Edge(cond, whenTrue));
    edges.push_back(CFG::Edge(NULL, whenFalse)); // negate cond
  }

  virtual void codegen(CodegenPass* p) {
    ASSERT(false) << "ConditionalBranch codegen not implemented";
  }
};

void CFG::addPredecessor(CFG* cfg) {
  this->predecessors.push_back(cfg);
}

void CFG::setTerminator(CFG::Terminator* newterminator) {
  this->terminator = newterminator;
}


CFG::Terminator* CFG::getTerminator() {
  ASSERT(terminator);
  return terminator;
}

void CFG::branchTo(CFG* next) {
  setTerminator(new UnconditionalBranch(next));
  next->addPredecessor(this);
}

void CFG::branchCond(ExprAST* cond, CFG* condTrue, CFG* condFalse) {
  setTerminator(new ConditionalBranch(cond, condTrue, condFalse));
  condTrue->addPredecessor(this);
  condFalse->addPredecessor(this);
}

llvm::BasicBlock* CFG::codegen(CodegenPass* p, llvm::Function* parentFunction) {
  if (ourBB) return ourBB;

  ASSERT(this->terminator) << "no terminator for BB from "
                           << str(this->parentAST);

  // Create our LLVM basic block
  ourBB = llvm::BasicBlock::Create(llvm::getGlobalContext(),
                                   this->suggestedName,
                                   parentFunction);

  // Create PHI node if we have multiple predecessors
  llvm::PHINode* phiNode = NULL;
  if (predecessors.size() >= 2) {
    EDiag() << "need to create phi node...";
    //phiNode = builder.CreatePHI(NULL, "phi");
  }

  // Codegen the body of the CFG node
  for (size_t i = 0; i < exprs.size(); ++i) {
    ExprAST* ast = exprs[i];
    ASSERT(ast != NULL);

    ast->accept(p);
    if (!isVoid(ast->value->getType())) {
      lastNonVoidValue = ast->value;
    }
  }

  // Codegen our successor basic blocks,
  // and whatever form of LLVM branch is needed to reach them.
  this->terminator->codegen(p);

  // Set incoming values for PHI node
  if (phiNode) {
    for (size_t i = 0; i < predecessors.size(); ++i) {
      CFG* pred = predecessors[i];
      phiNode->addIncoming(pred->lastNonVoidValue, pred->ourBB);
    }
  }
}

} // namespace foster

std::string getCFGEdgeSourceLabel(const CFG *cnode,
                                      CFG_succ_iterator I) {
  CFG* node = (CFG*) cnode;
  if (!node || !node->getTerminator()) { return ""; }

  // Label source of conditional branches with "T" or "F"
  if (const foster::ConditionalBranch* cb =
        dynamic_cast<foster::ConditionalBranch*>(node->getTerminator())) {

    size_t n = I - succ_begin(node);
    ExprAST* cond = cb->getEdgeCond(n);
    if (cond) {
      std::string s; llvm::raw_string_ostream ss(s);
      foster::prettyPrintExpr(cond, ss, 20);

      std::string condstr = pystring::replace(ss.str(), "\n", " ");
      condstr = pystring::replace(condstr, " < ", " LT ");
      condstr = pystring::replace(condstr, " > ", " GT ");
      if (!condstr.empty()) {
        return condstr;
      }
    } else if (I != succ_begin(node)) {
      return "else";
    }

    return string((I == succ_begin(node)) ? "T" : "F") + string(1, "0123456789"[n]);
  }

  return "";
}

