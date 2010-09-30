// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterSymbolTable.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"

#include "llvm/Value.h"
#include "llvm/Support/raw_ostream.h"

#include <sstream>

namespace foster {

SymbolTable<TypeAST> gTypeScope;
SymbolTable<ExprAST> gScope;

void gScopeInsert(const std::string& name, ExprAST* ast) {
  bool currentScopeHas = gScope._private_getCurrentScope()->thisLevelContains(name);
  if (!currentScopeHas) {
    gScope.insert(name, ast);
  } else {
    ExprAST* existing = gScope._private_getCurrentScope()->lookup(name);
    if (existing == ast) {
      llvm::outs() << "gScopeInsert(ExprAST " << name << ") was redundant!" << "\n";
    } else {
      llvm::outs() << "gScopeInsert(ExprAST " << name << ") had unexpected collision"
        << "\n\told: " << existing << " :: " << str(existing)
        << "\n\tnew: " <<      ast << " :: " << str(     ast)
        << "\n";
    }
  }
}


std::string
getFullSymbolInfoNodeLabel(
    const foster::SymbolTable<ExprAST>::LexicalScope* node,
    const foster::SymbolTable<ExprAST>* graph) {
  const char* newline = "\\l";
  std::stringstream ss;
  ss << node->getName() << "(@ " << node << ")";
  for (foster::SymbolTable<ExprAST>::LexicalScope::const_iterator
        it = node->begin(); it != node->end(); ++it) {
    std::pair<std::string, ExprAST*> p = *it;
    ExprAST* ast = p.second;

    ss << newline << p.first << ":" << ast;
    if (ast) { ss << ast->value; } else { ss << "NO value"; }
    ss << newline;
  }
  return ss.str();
}

////////////////////////////////////////////////////////////////////


std::string
getFullTypeASTNodeLabel(
    const foster::SymbolTable<TypeAST>::LexicalScope* node,
    const foster::SymbolTable<TypeAST>* graph) {
  const char* newline = "\\l";
  std::stringstream ss;

  ss << node->getName() << "(@ " << node << ")";
  for (foster::SymbolTable<TypeAST>::LexicalScope::const_iterator
        it = node->begin(); it != node->end(); ++it) {
    const std::string& name = it->first;
    TypeAST* t  = (*it).second;
    ss << newline << name << " : " << t;
  }
  return ss.str();
}

} // namespace foster
