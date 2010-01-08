// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

// Code duplication remover: every visitor header must include this list
// of class names, and the FosterASTVisitor class must include " = 0"
// pure virtual markers. Rather than copy/pasting the list n times...

#ifndef FOSTER_AST_VISITOR_DEFAULT_IMPL
#define FOSTER_AST_VISITOR_DEFAULT_IMPL
#endif

#define DECL_VISIT(type) \
  virtual void visit(type* ast) FOSTER_AST_VISITOR_DEFAULT_IMPL

DECL_VISIT(FnAST);
DECL_VISIT(SeqAST);
DECL_VISIT(BoolAST);
DECL_VISIT(CallAST);
DECL_VISIT(IntAST);
DECL_VISIT(IfExprAST);
DECL_VISIT(VariableAST);
DECL_VISIT(ArrayExprAST);
DECL_VISIT(PrototypeAST);
DECL_VISIT(TupleExprAST);
DECL_VISIT(SubscriptAST);
DECL_VISIT(UnpackExprAST);
DECL_VISIT(BinaryOpExprAST);
DECL_VISIT(BuiltinCompilesExprAST);

