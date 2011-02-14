// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "gtest/gtest.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/ProtobufToAST.h"
#include "parse/ParsingContext.h"
#include "passes/DumpToProtobuf.h"
#include "passes/PrettyPrintPass.h"

#include "base/LLVMUtils.h"
#include "parse/FosterTypeAST.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Constants.h"

#include <map>

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

foster::SourceRange testRange(NULL,
                              foster::SourceLocation(1, 2),
                              foster::SourceLocation(3, 4));

////////////////////////////////////////////////////////////////////

TypeAST* roundtrip(TypeAST* ty) {
  foster::fepb::Type t;
  DumpTypeToProtobufPass dp(&t);
  ty->accept(&dp);

  return foster::TypeAST_from_pb(&t);
}

//
//
// Test that simple non-compound types like i32 and void roundtrip properly.
//

TEST(ProtobufToAST, i32_type) {
  initCachedLLVMTypes();
  TypeAST* i32 = TypeAST::i(32);
  TypeAST* ri32 = roundtrip(i32);

  ASSERT_TRUE(i32);
  ASSERT_TRUE(ri32);

  ASSERT_EQ(i32->getLLVMType(), ri32->getLLVMType());
}

TEST(ProtobufToAST, void_type) {
  initCachedLLVMTypes();
  TypeAST* t = TypeAST::getVoid();
  TypeAST* rt = roundtrip(t);

  ASSERT_TRUE(t);
  ASSERT_TRUE(rt);

  ASSERT_EQ(t->getLLVMType(), rt->getLLVMType());
}

//
//
// Test that simple function types preserve their parts
// and their calling convention when roundtripping.
//

TEST(ProtobufToAST, fn_i32_to_i32_ccc_type) {
  initCachedLLVMTypes();
  TypeAST* i32 = TypeAST::i(32);
  std::vector<TypeAST*> args; args.push_back(i32);
  FnTypeAST* t = FnTypeAST::get(i32, args, "ccc");
  TypeAST* rt = roundtrip(t);

  ASSERT_TRUE(t);
  ASSERT_TRUE(rt);

  ASSERT_EQ(str(t->getLLVMType()), str(rt->getLLVMType()));

  FnTypeAST* rft = dynamic_cast<FnTypeAST*>(rt);
  ASSERT_TRUE(rft != NULL);

  EXPECT_EQ(t->getCallingConventionID(), rft->getCallingConventionID());
}

TEST(ProtobufToAST, fn_i32_to_i32_fastcc) {
  initCachedLLVMTypes();
  TypeAST* i32 = TypeAST::i(32);
  std::vector<TypeAST*> args; args.push_back(i32);
  FnTypeAST* t = FnTypeAST::get(i32, args, "fastcc");
  TypeAST* rt = roundtrip(t);

  ASSERT_TRUE(t);
  ASSERT_TRUE(rt);

  ASSERT_EQ(str(t->getLLVMType()), str(rt->getLLVMType()));

  FnTypeAST* rft = dynamic_cast<FnTypeAST*>(rt);
  ASSERT_TRUE(rft != NULL);

  EXPECT_EQ(t->getCallingConventionID(), rft->getCallingConventionID());
}

//
//
// Test that tuple types preserve their parts when roundtripping.
//

TEST(ProtobufToAST, tuple_i32_i32_type) {
  initCachedLLVMTypes();
  TypeAST* i32 = TypeAST::i(32);
  std::vector<TypeAST*> args;
  args.push_back(i32); args.push_back(TypeAST::i(64));
  TupleTypeAST* t = TupleTypeAST::get(args);
  TypeAST* rt = roundtrip(t);

  ASSERT_TRUE(t);
  ASSERT_TRUE(rt);

  ASSERT_EQ(str(t->getLLVMType()), str(rt->getLLVMType()));

  TupleTypeAST* rst = dynamic_cast<TupleTypeAST*>(rt);
  ASSERT_TRUE(rst != NULL);
}


////////////////////////////////////////////////////////////////////

foster::ParsingContext cc;

ExprAST* roundtrip(ExprAST* ast) {
  foster::ParsingContext::pushContext(&cc);

  foster::fepb::Expr e;
  DumpToProtobufPass dp(&e);
  ast->accept(&dp);

  ExprAST* rv = foster::ExprAST_from_pb(&e);
  foster::ParsingContext::popCurrentContext();
  return rv;
}

ExprAST* parse(const string& s) {
  unsigned errs = 0;
  ExprAST* rv = foster::parseExpr(s, errs, &cc);
  return errs == 0 ? rv : NULL;
}

string pr(ExprAST* ast) {
  std::string s; llvm::raw_string_ostream out(s);
  foster::prettyPrintExpr(ast, out, 55);
  return out.str();
}


//
//
// Test simple literals -- ints, bools.
//

TEST(ProtobufToAST, sm_int_literal_plain) {
  initCachedLLVMTypes();
  ExprAST* e = parse("123");
  ExprAST* re = roundtrip(e);

  IntAST* ie = dynamic_cast<IntAST*>(e);
  IntAST* ire = dynamic_cast<IntAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  ASSERT_EQ(ie->getOriginalText(), ire->getOriginalText());
}

TEST(ProtobufToAST, sm_int_literal_fancy_base2) {
  initCachedLLVMTypes();
  //                 0x  3  5
  ExprAST* e = parse("0011`0101_2");
  ExprAST* re = roundtrip(e);

  IntAST* ie = dynamic_cast<IntAST*>(e);
  IntAST* ire = dynamic_cast<IntAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  ASSERT_EQ(ie->getOriginalText(), ire->getOriginalText());
}

TEST(ProtobufToAST, lg_int_literal_fancy_base16) {
  initCachedLLVMTypes();
  ExprAST* e = parse("FEED`fAcE_16");
  ExprAST* re = roundtrip(e);

  IntAST* ie = dynamic_cast<IntAST*>(e);
  IntAST* ire = dynamic_cast<IntAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  ASSERT_EQ(ie->getOriginalText(), ire->getOriginalText());
}

// TODO: check "DEAD`FEED`FACE_16 when literals can have > 32 bits

TEST(ProtobufToAST, bool_literal_true) {
  initCachedLLVMTypes();
  ExprAST* e = parse("true");
  ExprAST* re = roundtrip(e);

  BoolAST* ie = dynamic_cast<BoolAST*>(e);
  BoolAST* ire = dynamic_cast<BoolAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  EXPECT_TRUE(ie->boolValue);
  EXPECT_TRUE(ire->boolValue);
}

//
//
// Test variables.
//

TEST(ProtobufToAST, unbound_variable) {
  initCachedLLVMTypes();
  ExprAST* e = new VariableAST("x", TypeAST::i(32), testRange);
  ExprAST* re = roundtrip(e);

  VariableAST* ie = dynamic_cast<VariableAST*>(e);
  VariableAST* ire = dynamic_cast<VariableAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  EXPECT_EQ("x", ie->name);
  EXPECT_EQ(ie->name, ire->name);

  EXPECT_EQ(testRange, ie->sourceRange);
  EXPECT_EQ(ie->sourceRange, ire->sourceRange);
}

//
//
// Test binary expressions.
//

TEST(ProtobufToAST, binop_plus) {
  initCachedLLVMTypes();
  ExprAST* e = parse("1 + 2");
  ExprAST* re = roundtrip(e);

  EXPECT_EQ(pr(e), pr(re));
}

//
//
// Test fuller examples.
//

TEST(ProtobufToAST, let_simple_arith) {
  initCachedLLVMTypes();
  ExprAST* e = parse("let x : i32 = 3 in { x + x * x }");

  ASSERT_TRUE(e);
  ExprAST* re = roundtrip(e);
  ASSERT_TRUE(re);

  EXPECT_EQ(pr(e), pr(re));
}

TEST(ProtobufToAST, let_lambda_call) {
  initCachedLLVMTypes();
  ExprAST* e = parse("let x : i32 = 3 \n"
                     "let f : fn (z:i32) = fn (z:i32) { z + 1 } in {\n"
                     "  f(x) }");
  ASSERT_TRUE(e);
  ExprAST* re = roundtrip(e);
  ASSERT_TRUE(re);

  EXPECT_EQ(pr(e), pr(re));
}

TEST(ProtobufToAST, fnlit_higher_order) {
  initCachedLLVMTypes();
  ExprAST* e = parse("fn (x : fn (z:i32) ) { 0 }");
  ASSERT_TRUE(e);
  ExprAST* re = roundtrip(e);
  ASSERT_TRUE(re);

  EXPECT_EQ(pr(e), pr(re));
}

#define STR(x) #x

TEST(ProtobufToAST, big_example_1) {
  initCachedLLVMTypes();
  ExprAST* e = parse(STR(
let x : i32 = 3 in {
  let f : fn (k:i32, h:i32, r:i32, m:i32) = fn (k:i32, h:i32, r:i32, m:i32) {
    let km : i32 = k * m in {
    let kx : i32 = bitxor(km, bitashr(km, r)) in {
      bitxor(h * m, kx * m)
    } }
  } in {
    f(x, x, x, x) ;  f(x, x, x, x)
  }
}
));
  ASSERT_TRUE(e);
  ExprAST* re = roundtrip(e);
  ASSERT_TRUE(re);

  EXPECT_EQ(pr(e), pr(re));
}

#undef STR


} // unnamed namespace


