// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "gtest/gtest.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/ProtobufToAST.h"
#include "parse/CompilationContext.h"
#include "passes/DumpToProtobuf.h"
#include "passes/PrettyPrintPass.h"

#include "llvm/Support/raw_ostream.h"

#include <map>

// terrible hack!
namespace foster {
extern std::map<std::string, const llvm::Type*> gCachedLLVMTypes;
}

namespace {

struct UnitTestBeginEnd {
  UnitTestBeginEnd() {
    foster::gCachedLLVMTypes["i32"] = TypeAST::i(32)->getLLVMType();
    foster::gCachedLLVMTypes["i64"] = TypeAST::i(64)->getLLVMType();
    foster::gCachedLLVMTypes["void"] = TypeAST::getVoid()->getLLVMType();
  }
  ~UnitTestBeginEnd() {

  }
} _ube;

foster::SourceRange testRange(NULL,
                              foster::SourceLocation(1, 2),
                              foster::SourceLocation(3, 4));

////////////////////////////////////////////////////////////////////

TypeAST* roundtrip(TypeAST* ty) {
  foster::pb::Type t;
  DumpTypeToProtobufPass dp(&t);
  ty->accept(&dp);

  return foster::TypeAST_from_pb(&t);
}

//
//
// Test that simple non-compound types like i32 and void roundtrip properly.
//

TEST(ProtobufToAST, i32_type) {
  TypeAST* i32 = TypeAST::i(32);
  TypeAST* ri32 = roundtrip(i32);

  ASSERT_TRUE(i32);
  ASSERT_TRUE(ri32);

  ASSERT_EQ(i32->getLLVMType(), ri32->getLLVMType());
}

TEST(ProtobufToAST, void_type) {
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

//
//
// Test small and large int type literals (needing 32..64 bits).
//

TEST(ProtobufToAST, literal_int_type_small) {
  LiteralIntValueTypeAST* t = LiteralIntValueTypeAST::get(42, testRange);

  TypeAST* rt = roundtrip(t);

  ASSERT_TRUE(t);
  ASSERT_TRUE(rt);

  ASSERT_EQ(str(t->getLLVMType()), str(rt->getLLVMType()));
  EXPECT_EQ(TypeAST::i(64)->getLLVMType(), t->getLLVMType());

  LiteralIntValueTypeAST* rst = dynamic_cast<LiteralIntValueTypeAST*>(rt);
  ASSERT_TRUE(rst != NULL);

  ASSERT_EQ(testRange, t->getSourceRange());
  ASSERT_EQ(t->getSourceRange(), rst->getSourceRange());


  ASSERT_EQ(t->getNumericalValue(), rst->getNumericalValue());
}

TEST(ProtobufToAST, literal_int_large) {
  LiteralIntValueTypeAST* t = LiteralIntValueTypeAST::get((1ULL << 42), testRange);
  TypeAST* rt = roundtrip(t);

  ASSERT_TRUE(t);
  ASSERT_TRUE(rt);

  ASSERT_EQ(str(t->getLLVMType()), str(rt->getLLVMType()));
  EXPECT_EQ(TypeAST::i(64)->getLLVMType(), t->getLLVMType());


  ASSERT_EQ(testRange, t->getSourceRange());
  ASSERT_EQ(t->getSourceRange(), rt->getSourceRange());


  LiteralIntValueTypeAST* rst = dynamic_cast<LiteralIntValueTypeAST*>(rt);
  ASSERT_TRUE(rst != NULL);

  ASSERT_EQ(t->getNumericalValue(), rst->getNumericalValue());
}

//
//
// Test simd vectors.
//

TEST(ProtobufToAST, simd_vector_type) {
  TypeAST* i32 = TypeAST::i(32);
  LiteralIntValueTypeAST* sz = LiteralIntValueTypeAST::get(4, testRange);
  SimdVectorTypeAST* t = SimdVectorTypeAST::get(sz, i32, testRange);
  TypeAST* rt = roundtrip(t);

  ASSERT_TRUE(t);
  ASSERT_TRUE(rt);
  ASSERT_EQ(str(t->getLLVMType()), str(rt->getLLVMType()));
  SimdVectorTypeAST* rst = dynamic_cast<SimdVectorTypeAST*>(rt);
  ASSERT_TRUE(rst != NULL);

  ASSERT_EQ(testRange, t->getSourceRange());
  ASSERT_EQ(t->getSourceRange(), rst->getSourceRange());

  ASSERT_EQ(t->getNumElements(), rst->getNumElements());
  ASSERT_EQ(t->getContainedType(0), rst->getContainedType(0));
}

//
//
// TODO Test closure types.
//
#if 0
TEST(ProtobufToAST, closure_type) {
  TypeAST* i32 = TypeAST::i(32);
  ClosureTypeAST* clty = new ClosureTypeAST(proto, unfuntype, testRange);
}
#endif

////////////////////////////////////////////////////////////////////

ExprAST* roundtrip(ExprAST* ast) {
  foster::pb::Expr e;
  DumpToProtobufPass dp(&e);
  ast->accept(&dp);

  return foster::ExprAST_from_pb(&e);
}

foster::CompilationContext cc;

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
  ExprAST* e = parse("123");
  ExprAST* re = roundtrip(e);

  IntAST* ie = dynamic_cast<IntAST*>(e);
  IntAST* ire = dynamic_cast<IntAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  ASSERT_EQ(ie->getOriginalText(), ire->getOriginalText());
  ASSERT_EQ(ie->getBase(), ire->getBase());

  ASSERT_EQ(123, ie->getAPInt().getZExtValue());
  ASSERT_EQ(123, ire->getAPInt().getZExtValue());
}

TEST(ProtobufToAST, sm_int_literal_fancy_base2) {
  //                 0x  3  5
  ExprAST* e = parse("0011`0101_2");
  ExprAST* re = roundtrip(e);

  IntAST* ie = dynamic_cast<IntAST*>(e);
  IntAST* ire = dynamic_cast<IntAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  ASSERT_EQ(ie->getOriginalText(), ire->getOriginalText());
  ASSERT_EQ(ie->getBase(), ire->getBase());
  ASSERT_EQ(2,             ire->getBase());

  ASSERT_EQ(0x35, ie->getAPInt().getZExtValue());
  ASSERT_EQ(0x35, ire->getAPInt().getZExtValue());
}

TEST(ProtobufToAST, lg_int_literal_fancy_base16) {
  ExprAST* e = parse("FEED`fAcE_16");
  ExprAST* re = roundtrip(e);

  IntAST* ie = dynamic_cast<IntAST*>(e);
  IntAST* ire = dynamic_cast<IntAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  ASSERT_EQ(ie->getOriginalText(), ire->getOriginalText());
  ASSERT_EQ(ie->getBase(), ire->getBase());
  ASSERT_EQ(16,            ire->getBase());

  ASSERT_EQ(0xFEEDFACEuLL, ie->getAPInt().getZExtValue());
  ASSERT_EQ(0xFEEDFACEuLL, ire->getAPInt().getZExtValue());
}

// TODO: check "DEAD`FEED`FACE_16 when literals can have > 32 bits

TEST(ProtobufToAST, bool_literal_true) {
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
// Test unary and binary expressions.
//

TEST(ProtobufToAST, unop_negate) {
  ExprAST* e = parse("-2");
  ExprAST* re = roundtrip(e);

  UnaryOpExprAST* ie = dynamic_cast<UnaryOpExprAST*>(e);
  UnaryOpExprAST* ire = dynamic_cast<UnaryOpExprAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  EXPECT_EQ(ie->op, ire->op);
  EXPECT_EQ(pr(ie), pr(ire));
}

TEST(ProtobufToAST, binop_plus) {
  ExprAST* e = parse("1 + 2");
  ExprAST* re = roundtrip(e);

  BinaryOpExprAST* ie = dynamic_cast<BinaryOpExprAST*>(e);
  BinaryOpExprAST* ire = dynamic_cast<BinaryOpExprAST*>(re);

  ASSERT_TRUE(ie);
  ASSERT_TRUE(ire);

  EXPECT_EQ(ie->op, ire->op);
  EXPECT_EQ(pr(ie), pr(ire));
}

//
//
// Test fuller examples.
//

TEST(ProtobufToAST, let_simple_arith) {
  ExprAST* e = parse("let x : i32 = 3 in { x + x * x }");

  ASSERT_TRUE(e);
  ExprAST* re = roundtrip(e);
  ASSERT_TRUE(re);

  EXPECT_EQ(pr(e), pr(re));
}

TEST(ProtobufToAST, let_lambda_call) {
  ExprAST* e = parse("let x : i32 = 3 \n"
                     "let f : fn (z:i32) = fn (z:i32) { z + 1 } in {\n"
                     "  f(x) }");
  ASSERT_TRUE(e);
  ExprAST* re = roundtrip(e);
  ASSERT_TRUE(re);

  EXPECT_EQ(pr(e), pr(re));
}

TEST(ProtobufToAST, fnlit_higher_order) {
  ExprAST* e = parse("fn (x : fn (i64) ) { 0 }");
  ASSERT_TRUE(e);
  ExprAST* re = roundtrip(e);
  ASSERT_TRUE(re);

  EXPECT_EQ(pr(e), pr(re));
}

#define STR(x) #x

TEST(ProtobufToAST, big_example_1) {
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


