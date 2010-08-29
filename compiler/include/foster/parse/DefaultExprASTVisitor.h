// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_DEFAULT_EXPR_AST_VISITOR
#define FOSTER_DEFAULT_EXPR_AST_VISITOR

#include "parse/ExprASTVisitor.h" 

struct DefaultExprASTVisitor : public ExprASTVisitor {
  explicit DefaultExprASTVisitor() {}
  virtual ~DefaultExprASTVisitor() {}
  
  #include "parse/ExprASTVisitor.decls.inc.h"
};

#endif
