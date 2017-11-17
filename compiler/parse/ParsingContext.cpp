// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/FreshNameGenerator.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ParsingContext.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include "_generated_/fosterLexer.h"

#include <stack>
#include <map>
#include <list>

using std::map;
using std::string;

namespace foster {

  bool isNewlineToken(pANTLR3_COMMON_TOKEN tok) {
    return tok->type == NL;
  }

std::stack<ParsingContext*> gParsingContexts;


struct ParsingContext::Impl {
  FreshNameGenerator freshNames;

  SymbolTable<ExprAST> exprScope;
  SymbolTable<TypeAST> typeScope;

  std::list<std::string> bindingContexts;

  std::map<pANTLR3_BASE_TREE, pANTLR3_COMMON_TOKEN> startTokens;
  std::map<pANTLR3_BASE_TREE, pANTLR3_COMMON_TOKEN>   endTokens;

  std::map<const foster::InputFile*,
             std::vector<pANTLR3_COMMON_TOKEN> >   hiddenTokens;

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
  if (!gParsingContexts.empty()) {
    cc->impl->startTokens  = gParsingContexts.top()->impl->startTokens;
    cc->impl->endTokens    = gParsingContexts.top()->impl->endTokens;
    cc->impl->hiddenTokens = gParsingContexts.top()->impl->hiddenTokens;
  }
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

TypeAST* // static
ParsingContext::lookupType(const std::string& str) {
  ASSERT(!gParsingContexts.empty());
  ParsingContext* cc = gParsingContexts.top();
  return cc->impl->typeScope.lookup(str);
}

void // static
ParsingContext::insertType(const std::string& str, TypeAST* ast) {
  ASSERT(!gParsingContexts.empty());
  ParsingContext* cc = gParsingContexts.top();
  cc->impl->typeScope.insert(str, ast, "ParsingContext::insertType");
}

/////////////////////

std::string // static
ParsingContext::freshName(std::string like) {
  ASSERT(!foster::gParsingContexts.empty());

  return foster::gParsingContexts.top()->impl->freshNames.fresh(like);
}

/////////////////////

void // static
ParsingContext::pushCurrentBinding(std::string binder) {
  ASSERT(!foster::gParsingContexts.empty());
  foster::gParsingContexts.top()->impl->bindingContexts.push_back(binder);
}

void // static
ParsingContext::popCurrentBinding() {
  ASSERT(!foster::gParsingContexts.empty());
  foster::gParsingContexts.top()->impl->bindingContexts.pop_back();
}

std::string // static
ParsingContext::getCurrentBindings() {
  ASSERT(!foster::gParsingContexts.empty());
  std::list<std::string>& bcs =
  	 	 	  foster::gParsingContexts.top()->impl->bindingContexts;
  ASSERT(!bcs.empty());

  std::string rv;
  for (auto it : bcs) {
    if (rv.empty()) { rv = it; } else {
      rv = rv + "___" + it;
    }
  }
  return rv;
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

void
ParsingContext::sawHiddenToken(pANTLR3_COMMON_TOKEN tok) {
  ASSERT(!gParsingContexts.empty());
  gParsingContexts.top()->impl->hiddenTokens[gInputFile].push_back(tok);
}

void
ParsingContext::sawNonHiddenToken() {
  ASSERT(!gParsingContexts.empty());
  std::vector<pANTLR3_COMMON_TOKEN>& tokens
                       = gParsingContexts.top()->impl->hiddenTokens[gInputFile];
  if ((!tokens.empty()) && tokens.back()) tokens.push_back(NULL);
}

std::vector<pANTLR3_COMMON_TOKEN> // static
ParsingContext::getHiddenTokens() {
  ASSERT(!gParsingContexts.empty());
  return gParsingContexts.top()->impl->hiddenTokens[gInputFile];
}

void // static
ParsingContext::clearTokenBoundaries() {
  ASSERT(!gParsingContexts.empty());

  gParsingContexts.top()->impl->startTokens.clear();
  gParsingContexts.top()->impl->  endTokens.clear();
}

////////////////////////////////////////////////////////////////////

ParsingContext::ParsingContext() {
  impl = new Impl();
}

////////////////////////////////////////////////////////////////////

} // namespace foster

