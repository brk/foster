// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterSymbolTable.h"
#include "parse/FosterAST.h"

namespace foster {

SymbolTable<TypeAST> gTypeScope;
SymbolTable<SymbolInfo> gScope;

llvm::Value* gScopeLookupValue(const std::string& str) {
  SymbolInfo* info = gScope.lookup(str, "");
  return info ? info->value : NULL;
}

ExprAST* gScopeLookupAST(const std::string& str) {
  SymbolInfo* info = gScope.lookup(str, "");
  return info ? info->ast : NULL;
}

void gScopeInsert(const std::string& name, llvm::Value* val) {
  bool currentScopeHas = gScope._private_getCurrentScope()->thisLevelContains(name);
  if (!currentScopeHas) {
    gScope.insert(name, new SymbolInfo(val));
  } else {
    SymbolInfo* info = gScope._private_getCurrentScope()->lookup(name, "");
    if (info->value && info->value != val) {
      std::cerr << "gScopeInsert(Value " << name << ") had unexpected collision "
          << "old: " << str(info->value)
          << "new: " << str(val)
          << std::endl;
    } else if (info->value && info->value == val) {
      std::cerr << "gScopeInsert(Value " << name << ") was redundant" << std::endl;
    } else {
      info->value = val;
    }
  }
}

void gScopeInsert(const std::string& name, ExprAST* ast) {
  bool currentScopeHas = gScope._private_getCurrentScope()->thisLevelContains(name);
  if (!currentScopeHas) {
    gScope.insert(name, new SymbolInfo(ast));
  } else {
    SymbolInfo* info = gScope._private_getCurrentScope()->lookup(name, "");
    if (info->ast) {
      std::cerr << "gScopeInsert(ExprAST " << name << ") had unexpected collision"
          << std::endl;
    } else {
      info->ast = ast;
    }
  }
}


std::string
getFullSymbolInfoNodeLabel(
    const foster::SymbolTable<foster::SymbolInfo>::LexicalScope* node,
    const foster::SymbolTable<foster::SymbolInfo>* graph) {
  const char* newline = "\\l";
  std::stringstream ss;
  ss << node->getName() << "(@ " << node << ")";
  for (foster::SymbolTable<foster::SymbolInfo>::LexicalScope::const_iterator
        it = node->begin(); it != node->end(); ++it) {
    std::pair<std::string, foster::SymbolInfo*> p = *it;
    ExprAST* ast = p.second->ast;
    const llvm::Value* v = p.second->value;

    if (false) {
      std::cout << p.first << " : " << v << " : " << "; ast: " << ast;
      std::flush(std::cout);
      if (v) {std::cout << v->getRawType()->getDescription() << std::endl;}
    }

    ss << newline << p.first << ":" << newline
        << "    ast:       " << ast
          << "; ast->value: ";

    if (ast) { ss << ast->value; } else { ss << "NO value"; }

    ss << newline;

    ss << "     v: " << v << "; LLVM type: " <<
       std::string(v ? v->getRawType()->getDescription() : "<no llvm::Value>");
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
