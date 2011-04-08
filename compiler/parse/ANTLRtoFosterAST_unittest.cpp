// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"
#include "parse/FosterAST.h"
#include "passes/PrettyPrintPass.h"
#include "parse/FosterTypeAST.h"

#include "llvm/Support/raw_ostream.h"

#include "pystring/pystring.h"

#include "gtest/gtest.h"

#include <sstream>

using std::string;

foster::ParsingContext cc;

namespace foster {
  extern std::map<std::string, const llvm::Type*> gCachedLLVMTypes;
}

namespace {

void initCachedLLVMTypes() {
  static bool done = false;
  if (done) return;
  done = true;
  foster::gCachedLLVMTypes["i32"] = TypeAST::i(32)->getLLVMType();
  foster::gCachedLLVMTypes["i64"] = TypeAST::i(64)->getLLVMType();
  foster::gCachedLLVMTypes["void"] = TypeAST::getVoid()->getLLVMType();
}


ExprAST* parse(const string& s) {
  unsigned errs = 0;
  ExprAST* rv = foster::parseExpr(s, errs, &cc);
  return errs == 0 ? rv : NULL;
}

string pr(ExprAST* ast) {
  std::string s; llvm::raw_string_ostream out(s);
  foster::ParsingContext::pushContext(&cc);
  foster::prettyPrintExpr(ast, out, 55);
  foster::ParsingContext::popCurrentContext();
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

  EXPECT_EQ("(3 * 4) <= 2",
    pr(parse("3 * 4  <= 2")));
}

TEST(ANTLRtoFosterAST, arithPrecedence) {
  EXPECT_EQ("2 + (3 * 4)",
    pr(parse("2 + 3 * 4")));

  EXPECT_EQ("(2 * 3) + 4",
    pr(parse("(2 * 3) + 4")));

  EXPECT_EQ("(2 + 3) * 4",
    pr(parse("(2 + 3) * 4")));

  EXPECT_EQ("2 + (3 / 4)",
    pr(parse("2 + 3 / 4")));

  EXPECT_EQ("(2 / 3) + 4",
    pr(parse("(2 / 3) + 4")));

  EXPECT_EQ("2 + (3 / 4)",
    pr(parse("2 + 3 / 4")));

  EXPECT_EQ("((1 + (2 * 3)) + (4 * 5)) + 6",
    pr(parse("1 + 2 * 3 + 4 * 5 + 6")));

  EXPECT_EQ("(1 + (2 * 3)) + ((4 * 5) * 6)",
    pr(parse("1 + 2 * 3 + 4 * 5 * 6")));

  EXPECT_EQ("((0 + 1) + (2 * 3)) + ((4 * 5) * 6)",
    pr(parse("0 + 1 + 2 * 3 + 4 * 5 * 6")));
}

TEST(ANTLRtoFosterAST, colonCommaArrow) {
/*
  EXPECT_EQ("(k : v), (k : (x -> y))",
    pr(parse("k : v, k : x -> y")));
*/
}

TEST(ANTLRtoFosterAST, first_order_types_simple_correct) {
  initCachedLLVMTypes();
  EXPECT_EQ(0,
      pystring::count("opaque",
                      pr(parse("fn (x : i32 to i32) { 0 }")))
  );
}

TEST(ANTLRtoFosterAST, higher_order_types_simple_correct) {
  initCachedLLVMTypes();
  EXPECT_EQ(0,
      pystring::count(pr(parse("fn (x : fn (z:i64 to i32) to i32) { 0 }")),
                      "opaque")
  );
}

TEST(ANTLRtoFosterAST, higher_order_types_simple_incorrect) {
  initCachedLLVMTypes();
  // equivalent to "fn (x : fn (i64:i32)) { 0 }"
  string s = pr(parse("fn (x : fn (i64 to i32) to i32) { 0 }"));
  EXPECT_EQ(0, pystring::count(s, "opaque"));
}

} // unnamed namespace

