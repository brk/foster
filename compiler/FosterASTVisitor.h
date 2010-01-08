// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b3f256206be38_88233154
#define H_4b3f256206be38_88233154

struct FnAST;
struct SeqAST;
struct BoolAST;
struct CallAST;
struct IntAST ;
struct IfExprAST;
struct VariableAST;
struct ArrayExprAST;
struct PrototypeAST;
struct TupleExprAST;
struct SubscriptAST;
struct BinaryExprAST;
struct BuiltinCompilesExprAST;

struct FosterASTVisitor {
  virtual void visit(FnAST* ast) = 0;
  virtual void visit(SeqAST* ast) = 0;
  virtual void visit(BoolAST* ast) = 0;
  virtual void visit(CallAST* ast) = 0;
  virtual void visit(IntAST*  ast) = 0;
  virtual void visit(IfExprAST* ast) = 0;
  virtual void visit(VariableAST* ast) = 0;
  virtual void visit(ArrayExprAST* ast) = 0;
  virtual void visit(PrototypeAST* ast) = 0;
  virtual void visit(TupleExprAST* ast) = 0;
  virtual void visit(SubscriptAST* ast) = 0;
  virtual void visit(BinaryExprAST* ast) = 0;
  virtual void visit(BuiltinCompilesExprAST* ast) = 0;
};

#include "FosterAST.h"

#endif // header guard

