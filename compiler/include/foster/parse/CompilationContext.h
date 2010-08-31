// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_COMPILATION_CONTEXT_H
#define FOSTER_COMPILATION_CONTEXT_H

#include "llvm/Support/IRBuilder.h"

#include "parse/OperatorPrecedence.h"

#include "antlr3interfaces.h"

#include <string>

namespace llvm {
  class Module;
  class ExecutionEngine;
  class raw_ostream;
}

struct TypeAST;

// Defined in ANTLRtoFosterAST.cpp; the header
// is not #included due to ANTLR macro conflicts.
void initMaps();

std::string freshName(std::string like);

namespace foster {

void initializeLLVM();


class CompilationContext {
public:
  CompilationContext();

public:
  static CompilationContext*
  pushNewContext();
  
  static void
  pushContext(CompilationContext*);
  
  static CompilationContext*
  popCurrentContext();
  
  /////////////////////
  
  static std::string
  freshName(std::string likeThisOne);
  
  /////////////////////

  static void
  setTokenRange(pANTLR3_BASE_TREE t,
                pANTLR3_COMMON_TOKEN s,
                pANTLR3_COMMON_TOKEN e);
  
  static pANTLR3_COMMON_TOKEN
  getStartToken(pANTLR3_BASE_TREE t);
  
  static pANTLR3_COMMON_TOKEN
  getEndToken(pANTLR3_BASE_TREE t);
  
  static void
  clearTokenBoundaries();
  
  ///////////////////
  
  static foster::OperatorPrecedenceTable::OperatorRelation
  getOperatorRelation(const std::string& op1, const std::string& op2);
  
  static bool
  isKnownOperatorName(const std::string& op);
  
  ///////////////////
  
  // Seeing if it's useful for individual unit tests to redirect all output
  // to a string, so it can be (A) hidden from the console unless needed, and
  // (B) inspected to verify the presence/absence of specific errors.
  //llvm::raw_ostream& currentErrs();
  //llvm::raw_ostream& currentOuts();
  //void redirectErrsAndOutsTo(llvm::raw_ostream&);
  
private:
  struct Impl;
  Impl* impl;
};


extern llvm::ExecutionEngine* ee;
extern llvm::IRBuilder<> builder;
extern llvm::Module* module;

TypeAST* TypeASTFor(const std::string& name);
const llvm::Type* LLVMTypeFor(const std::string& name);

} // namespace foster

#endif
