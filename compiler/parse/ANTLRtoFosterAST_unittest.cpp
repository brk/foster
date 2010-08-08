// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/ANTLRtoFosterAST.h"
#include "parse/FosterAST.h"
#include "passes/PrettyPrintPass.h"

#include "gtest/gtest.h"

#include <sstream>

using std::string;

foster::CompilationContext cc;

namespace {
  
ExprAST* parse(const string& s) {
  unsigned errs = 0;
  ExprAST* rv = foster::parseExpr(s, errs, &cc);
  return errs == 0 ? rv : NULL;
}

string pr(ExprAST* ast) {
  std::stringstream out;
  { PrettyPrintPass p(out, 55); p.emit(ast); }
  return out.str();
}

TEST(ANTLRtoFosterAST, basics) {
  EXPECT_TRUE(parse("true") != NULL);
  EXPECT_TRUE(dynamic_cast<BoolAST*>(parse("true")));
  EXPECT_EQ("true", pr(parse("true")));
  
  EXPECT_TRUE(parse("123") != NULL);
  EXPECT_TRUE(dynamic_cast<IntAST*>(parse("123")));
  EXPECT_EQ("1234", pr(parse("1234")));
}

TEST(ANTLRtoFosterAST, respectsExplictParens) {
  EXPECT_EQ("(true)",
    pr(parse("(true)")));
}

TEST(ANTLRtoFosterAST, arithPrecedenceInParens) {
  EXPECT_EQ("(3 + ((2 + (3 * 4)) * 1)) + 2",
    pr(parse("3 + (2 + 3 * 4) * 1 + 2")));

  EXPECT_EQ("(3 + (((3 * 4) + 2) * 1)) + 2",
    pr(parse("3 + (3 * 4 + 2) * 1 + 2")));
}


TEST(ANTLRtoFosterAST, arithCmpPrecedence) {
  EXPECT_EQ("2 <= (3 * 4)",
    pr(parse("2 <= 3 * 4")));
}

TEST(ANTLRtoFosterAST, arithPrecedence) {
  EXPECT_EQ("2 + (3 * 4)",
    pr(parse("2 + 3 * 4")));

  EXPECT_EQ("(2 + 3) * 4",
    pr(parse("(2 + 3) * 4")));
  
  EXPECT_EQ("((1 + (2 * 3)) + (4 * 5)) + 6",
    pr(parse("1 + 2 * 3 + 4 * 5 + 6")));
  
  EXPECT_EQ("(1 + (2 * 3)) + ((4 * 5) * 6)",
    pr(parse("1 + 2 * 3 + 4 * 5 * 6")));
  
  EXPECT_EQ("((0 + 1) + (2 * 3)) + ((4 * 5) * 6)",
    pr(parse("0 + 1 + 2 * 3 + 4 * 5 * 6")));
}


} // unnamed namespace

