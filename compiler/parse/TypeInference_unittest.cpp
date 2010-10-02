// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "gtest/gtest.h"

#include "parse/ANTLRtoFosterAST.h"
#include "passes/TypecheckPass.h"
#include "passes/PrettyPrintPass.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ParsingContext.h"

#include "llvm/Support/raw_ostream.h"

#include <map>
#include <string>

using std::string;

// terrible hack!
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


ExprAST* parse(foster::ParsingContext& cc, const string& s) {
  unsigned errs = 0;
  ExprAST* rv = foster::parseExpr(s, errs, &cc);
  return errs == 0 ? rv : NULL;
}


ExprAST* elaborate(foster::ParsingContext& cc, ExprAST* e) {
  if (e) {
    foster::ParsingContext::pushContext(&cc);
    foster::typecheck(e);
    foster::ParsingContext::popCurrentContext();
  }
  return e;
}

string pr(ExprAST* ast) {
  std::string s; llvm::raw_string_ostream out(s);
  foster::prettyPrintExpr(ast, out, 55);
  return out.str();
}

#define STR(x) #x

////////////////////////////////////////////////////////////////////

TEST(TypeInference, parallel_compilation_contexts) {
  initCachedLLVMTypes();
  foster::ParsingContext cc1; cc1.startAccumulatingOutputToString();
  foster::ParsingContext cc2; cc2.startAccumulatingOutputToString();

  ExprAST* e1a = parse(cc1, STR(
let x : i32 = 3 in {
  x
}
));


  ExprAST* e2a = parse(cc2, STR(
let x : i32 = 3 in {
  x
}
  ));

  ExprAST* e1b = parse(cc1, STR(
let x : i32 = 3 in {
  x
}
  ));

  ASSERT_NE(pr(e1a), pr(e1b));
  EXPECT_EQ(pr(e1a), pr(e2a));
}

////////////////////////////////////////////////////////////////////

TEST(TypeInference, i32_handling_simple_closure0) {
  initCachedLLVMTypes();
  foster::ParsingContext cc1; cc1.startAccumulatingOutputToString();
  foster::ParsingContext cc2; cc2.startAccumulatingOutputToString();

  ExprAST* ae = parse(cc1, STR(
let x : i32 = 3 in {
  let f : fn (m:i32) = fn (m:i32 to i32) { m } in {
    f(x)
  }
}
));
  ASSERT_TRUE(ae);
  ExprAST* eae = elaborate(cc1, ae);


  ExprAST* ue = parse(cc2, STR(
let x = 3 in {
  let f : fn (m:i32) = fn (m : i32) { m } in {
    f(x)
  }
}
));
  ASSERT_TRUE(ue);
  ExprAST* ee = elaborate(cc2, ue);
  ASSERT_TRUE(ee);

  EXPECT_EQ(pr(eae), pr(ee));
}

////////////////////////////////////////////////////////////////////
/** temporarily disabled
TEST(TypeInference, i32_handling_simple_closure1) {
  initCachedLLVMTypes();
  foster::ParsingContext cc1; cc1.startAccumulatingOutputToString();
  foster::ParsingContext cc2; cc2.startAccumulatingOutputToString();

  ExprAST* ae = parse(cc1, STR(
let x : i32 = 3 in {
  let f : fn (m:i32) = fn (m:i32 to i32) { m } in {
    f(x)
  }
}
));
  ASSERT_TRUE(ae);
  ExprAST* eae = elaborate(cc1, ae);


  ExprAST* ue = parse(cc2, STR(
let x = 3 in {
  let f = fn (m : i32) { m } in {
    f(x)
  }
}
));
  ASSERT_TRUE(ue);
  ExprAST* ee = elaborate(cc2, ue);
  ASSERT_TRUE(ee);

  EXPECT_EQ(pr(eae), pr(ee));
}

////////////////////////////////////////////////////////////////////

// as above, but without the annotation on the inner function
TEST(TypeInference, i32_handling_simple_closure2) {
  initCachedLLVMTypes();
  foster::ParsingContext cc1; cc1.startAccumulatingOutputToString();
  foster::ParsingContext cc2; cc2.startAccumulatingOutputToString();

  ExprAST* ae = parse(cc1, STR(
let vx : i32 = 3 in {
  let vf : fn (vm:i32) = fn (vm:i32 to i32) { vm } in {
    vf(vx)
  }
}
));
  ASSERT_TRUE(ae);
  ExprAST* eae = elaborate(cc1, ae);

  foster::currentOuts() << "================ parse boundary ================\n";

  ExprAST* ue = parse(cc2, STR(
let vx = 3 in {
  let vf = fn (vm) { vm } in {
    vf(vx)
  }
}
));
  ASSERT_TRUE(ue);
  ExprAST* ee = elaborate(cc2, ue);
  ASSERT_TRUE(ee);

  EXPECT_EQ(pr(eae), pr(ee));
}
**/


#undef STR


} // unnamed namespace


