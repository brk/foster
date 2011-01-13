// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/FreshNameGenerator.h"

#include "parse/FosterTypeAST.h"
#include "parse/FosterSymbolTable.h"
#include "parse/ParsingContext.h"

#include "llvm/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <stack>
#include <map>

using llvm::getGlobalContext;

using std::map;
using std::string;

namespace foster {

std::stack<ParsingContext*> gParsingContexts;


struct ParsingContext::Impl {
  OperatorPrecedenceTable prec;
  FreshNameGenerator freshNames;

  std::map<pANTLR3_BASE_TREE, pANTLR3_COMMON_TOKEN> startTokens;
  std::map<pANTLR3_BASE_TREE, pANTLR3_COMMON_TOKEN>   endTokens;

  std::string accumulated_output;
  llvm::raw_string_ostream os;
  llvm::raw_ostream* outs;
  llvm::raw_ostream* errs;

  std::map<string, bool> keywords;
  std::map<string, bool> reserved_keywords;

  std::map<ExprAST*, ExprAST*> parents;

  Impl() : os(accumulated_output), outs(NULL), errs(NULL) {
    initMaps();
  }

private:
  void initMaps();
};


#ifndef ARRAY_SIZE
#define ARRAY_SIZE(a) (sizeof(a)/sizeof(((a)[0])))
#endif

namespace {
  const char* c_keywords[] = {
    "as" , "at" , "def" , "id", "in", "is", "it", "to",
    "given" , "false" , "if" , "match" , "do" , "new" , "nil",
    "gives" , "and" , "or" , "true" , "var" , "while",
    "for", "ref", "?ref"
  };
  const char* c_reserved_keywords[] = {
    "def", "catch", "lazy", "object", "package", "private",
    "protected", "return", "throw", "trait", "try", "type",
    "val", "with", "yield", "except"
  };
} // unnamed namespace

void
ParsingContext::Impl::initMaps() {
  for (size_t i = 0; i < ARRAY_SIZE(c_keywords); ++i) {
    keywords[c_keywords[i]] = true;
  }

  for (size_t i = 0; i < ARRAY_SIZE(c_reserved_keywords); ++i) {
    reserved_keywords[c_reserved_keywords[i]] = true;
  }
}


ParsingContext* // static
ParsingContext::pushNewContext() {
  ParsingContext* cc = new ParsingContext();
  gParsingContexts.push(cc);
  return cc;
}

void // static
ParsingContext::pushContext(ParsingContext* cc) {
  gParsingContexts.push(cc);
}

ParsingContext* // static
ParsingContext::popCurrentContext() {
  ASSERT(!gParsingContexts.empty());
  ParsingContext* cc = gParsingContexts.top();
  gParsingContexts.pop();
  return cc;
}

/////////////////////

std::string // static
ParsingContext::freshName(std::string like) {
  ASSERT(!foster::gParsingContexts.empty());

  return foster::gParsingContexts.top()->impl->freshNames.fresh(like);
}

/////////////////////

void // static
ParsingContext::setTokenRange(pANTLR3_BASE_TREE t,
              pANTLR3_COMMON_TOKEN s,
              pANTLR3_COMMON_TOKEN e) {
  ASSERT(!gParsingContexts.empty());

  gParsingContexts.top()->impl->startTokens[t] = s;
  gParsingContexts.top()->impl->  endTokens[t] = e;
}

pANTLR3_COMMON_TOKEN // static
ParsingContext::getStartToken(pANTLR3_BASE_TREE t) {
  ASSERT(!gParsingContexts.empty());

  return gParsingContexts.top()->impl->startTokens[t];
}

pANTLR3_COMMON_TOKEN // static
ParsingContext::getEndToken(pANTLR3_BASE_TREE t) {
  ASSERT(!gParsingContexts.empty());

  return gParsingContexts.top()->impl->endTokens[t];
}


void // static
ParsingContext::clearTokenBoundaries() {
  ASSERT(!gParsingContexts.empty());

  gParsingContexts.top()->impl->startTokens.clear();
  gParsingContexts.top()->impl->  endTokens.clear();
}

///////////////////

foster::OperatorPrecedenceTable::OperatorRelation // static
ParsingContext::getOperatorRelation(const std::string& op1,
                                        const std::string& op2) {
  ASSERT(!gParsingContexts.empty());

  return gParsingContexts.top()->impl->prec.get(op1, op2);
}

bool // static
ParsingContext::isKnownOperatorName(const string& op) {
  ASSERT(!gParsingContexts.empty());

  return gParsingContexts.top()->impl->prec.isKnownOperatorName(op);
}

bool // static
ParsingContext::isKeyword(const string& op) {
  ASSERT(!gParsingContexts.empty());

  return gParsingContexts.top()->impl->keywords[op];
}

bool // static
ParsingContext::isReservedKeyword(const string& op) {
  ASSERT(!gParsingContexts.empty());

  return gParsingContexts.top()->impl->reserved_keywords[op];
}

////////////////////////////////////////////////////////////////////

void // static
ParsingContext::setParent(ExprAST* child, ExprAST* parent) {
  ASSERT(!gParsingContexts.empty());

  gParsingContexts.top()->impl->parents[child] = parent;
}

ExprAST* // static
ParsingContext::getParent(ExprAST* child) {
  if (gParsingContexts.empty()) { return NULL; }

  return gParsingContexts.top()->impl->parents[child];
}

////////////////////////////////////////////////////////////////////

ParsingContext::ParsingContext() {
  impl = new Impl();
}

////////////////////////////////////////////////////////////////////

DDiag::~DDiag() {}

////////////////////////////////////////////////////////////////////

map<string, const llvm::Type*> gCachedLLVMTypes;

TypeAST* TypeASTFor(const string& name) {
  if (gCachedLLVMTypes.count(name) == 1) {
    return NamedTypeAST::get(name, gCachedLLVMTypes[name]);
  } else if (TypeAST* ty = gTypeScope.lookup(name)) {
    return ty;
  } else {
    return NULL;
  }
}

void ParsingContext::initCachedLLVMTypeNames() {
  gCachedLLVMTypes["i1"] = llvm::IntegerType::get(getGlobalContext(), 1);
  gCachedLLVMTypes["i8"] = llvm::IntegerType::get(getGlobalContext(), 8);
  gCachedLLVMTypes["i16"] = llvm::IntegerType::get(getGlobalContext(), 16);
  gCachedLLVMTypes["i32"] = llvm::IntegerType::get(getGlobalContext(), 32);
  gCachedLLVMTypes["i64"] = llvm::IntegerType::get(getGlobalContext(), 64);

  gCachedLLVMTypes["i8*"] = llvm::PointerType::getUnqual(gCachedLLVMTypes["i8"]);
  gCachedLLVMTypes["i8**"] = llvm::PointerType::getUnqual(gCachedLLVMTypes["i8*"]);
}

} // namespace foster

string freshName(string like) {
  return foster::ParsingContext::freshName(like);
}

