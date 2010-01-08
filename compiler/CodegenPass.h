// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b3f24ef542273_50678977
#define H_4b3f24ef542273_50678977

#include "FosterASTVisitor.h"

struct CodegenPass : public FosterASTVisitor {
  virtual void visit(FnAST* ast);
  virtual void visit(SeqAST* ast);
  virtual void visit(BoolAST* ast);
  virtual void visit(CallAST* ast);
  virtual void visit(IntAST*  ast);
  virtual void visit(IfExprAST* ast);
  virtual void visit(VariableAST* ast);
  virtual void visit(PrototypeAST* ast);
  virtual void visit(TupleExprAST* ast);
  virtual void visit(SubscriptAST* ast);
  virtual void visit(BinaryExprAST* ast);
  virtual void visit(BuiltinCompilesExprAST* ast);
};

#endif // header guard


  
