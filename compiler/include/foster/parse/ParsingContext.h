// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PARSING_CONTEXT_H
#define FOSTER_PARSING_CONTEXT_H

#include "base/Diagnostics.h"

#include "parse/FosterSymbolTable.h"
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

namespace foster {

  bool isNewlineToken(pANTLR3_COMMON_TOKEN tok);

class ParsingContext {
public:
  explicit ParsingContext();

public:
  static ParsingContext*
  pushNewContext();

  static void
  pushContext(ParsingContext*);

  static ParsingContext*
  popCurrentContext();

  /////////////////////

  static TypeAST*
  lookupType(const std::string& str);

  static void
  insertType(const std::string& str, TypeAST* ast);

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
  sawHiddenToken(pANTLR3_COMMON_TOKEN tok);

  static void
  sawNonHiddenToken(); // generate fake hidden token marker

  static std::vector<pANTLR3_COMMON_TOKEN> // with NULL pointers marking non-hidden tokens
  getHiddenTokens();

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

  /////////////////////

private:
  struct Impl;
  Impl* impl;
};

} // namespace foster

#endif
