// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_CFG_H
#define FOSTER_CFG_H

#include "llvm/Support/CFG.h"
#include "llvm/Support/GraphWriter.h"

#include <vector>
#include <utility>
#include <sstream>

struct ExprAST;
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

using foster::CFG;

typedef llvm::SuccIterator<CFG::Terminator*, CFG> CFG_succ_iterator;

inline CFG_succ_iterator succ_begin(CFG* cfg) {
  return CFG_succ_iterator(cfg->getTerminator());
}

inline CFG_succ_iterator succ_end(CFG* cfg) {
  return CFG_succ_iterator(cfg->getTerminator(), true);
}

std::string getCFGEdgeSourceLabel(const CFG *node,
                               CFG_succ_iterator I);

namespace llvm {

template <> struct GraphTraits<CFG*> {
  typedef CFG                  NodeType;
  typedef CFG_succ_iterator    ChildIteratorType;

  static NodeType* getEntryNode(CFG* cfg) { return cfg; }
  static inline ChildIteratorType child_begin(NodeType* n) {
    return ::succ_begin(n);
  }
  static inline ChildIteratorType child_end(NodeType* n) {
    return ::succ_end(n);
  }
};

template <> struct GraphTraits<FnAST*>
          : public GraphTraits<CFG*> {
  static NodeType* getEntryNode(FnAST* f) { return f->cfgs[0]; }

  typedef std::vector<CFG*>::iterator    nodes_iterator;
  static nodes_iterator nodes_begin(FnAST* f) { return f->cfgs.begin(); }
  static nodes_iterator nodes_end  (FnAST* f) { return f->cfgs.end(); }
};


template <> struct DOTGraphTraits<FnAST*> : public DefaultDOTGraphTraits {

  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(const FnAST* fnast) {
    return string("CFG for ") + fnast->proto->name;
  }

  static std::string getSimpleNodeLabel(const CFG* node,
                                        const FnAST* graph) {
    std::stringstream ss;
    ss << node->getBlockName() << "(@ " << node << ")";
    return ss.str();
  }

  std::string getNodeLabel(const CFG* node, const FnAST* graph) {
    return getSimpleNodeLabel(node, graph);
  }


  static std::string getEdgeSourceLabel(const CFG *node,
                                        CFG_succ_iterator I) {
    return getCFGEdgeSourceLabel(node, I);
  }
};

} // namespace llvm

#endif
