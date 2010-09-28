// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_COMPILATION_CONTEXT_H
#define FOSTER_COMPILATION_CONTEXT_H

#include "llvm/Support/IRBuilder.h"

#include "base/Diagnostics.h"

#include "parse/OperatorPrecedence.h"

#include "antlr3interfaces.h"

#include <string>
#include <set>

namespace llvm {
  class Module;
  class raw_ostream;
}

struct ExprAST;
struct TypeAST;

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

  static bool
  isKeyword(const std::string& op);

  static bool
  isReservedKeyword(const std::string& op);

  ///////////////////

  static void
  setParent(ExprAST* child, ExprAST* parent);

  static ExprAST*
  getParent(ExprAST* child);

  /////////////////////


  // Seeing if it's useful for individual unit tests to redirect all output
  // to a string, so it can be (A) hidden from the console unless needed, and
  // (B) inspected to verify the presence/absence of specific errors.
  llvm::raw_ostream& currentErrs();
  llvm::raw_ostream& currentOuts();
  void startAccumulatingOutputToString();
  std::string collectAccumulatedOutput();

  /////////////////////

private:
  struct Impl;
  Impl* impl;
};


extern llvm::IRBuilder<> builder;
extern llvm::Module* module;

TypeAST* TypeASTFor(const std::string& name);
const llvm::Type* LLVMTypeFor(const std::string& name);

////////////////////////////////////////////////////////////////////

// Global version of above methods on CompilationContext, for use by
// the diagnostic builders.
// These functions default to llvm::*() if there's no current context.

llvm::raw_ostream& currentErrs();
llvm::raw_ostream& currentOuts();

// For want of a better place to put them...
extern bool gDebugLoggingEnabled;
extern std::set<std::string> gEnabledDebuggingTags;

llvm::raw_ostream& dbg(const std::string& tag);

////////////////////////////////////////////////////////////////////

// Error diagnostic builder; unlike foster::SimpleEDiag, can be re-routed.
class EDiag : public DiagBase {
public:
  explicit EDiag();
  virtual ~EDiag();
private:
  EDiag(const EDiag&);
};

// Debug diagnostic builder
class DDiag : public DiagBase {
public:
  explicit DDiag(llvm::raw_ostream::Colors _color)
                   : DiagBase(foster::currentErrs(), "debug") {
    this->color = _color;
  }
  explicit DDiag() : DiagBase(foster::currentErrs(), "debug") {}
  virtual ~DDiag();
private:
  DDiag(const DDiag&);
};

} // namespace foster

#endif
