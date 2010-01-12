// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b3f256206be38_88233154
#define H_4b3f256206be38_88233154

struct ExprAST;

// Forward-declare all the AST node types
#define FOSTER_AST_VISITOR_GEN(type) struct type;
#include "FosterASTVisitor.decls.inc.h"
#undef  FOSTER_AST_VISITOR_GEN

struct FosterASTVisitor {
  virtual void visitChildren(ExprAST* ast);

  // Declare the individual (pure virtual) visit function for the AST node types
  #define FOSTER_AST_VISITOR_PURE_VIRTUAL
  #include "FosterASTVisitor.decls.inc.h"
  #undef  FOSTER_AST_VISITOR_PURE_VIRTUAL
};

// This has to be included after the declaration for FosterASTVisitor
// because the classes in FosterAST depend on these declarations for
// the double-dispatch portion of the Visitor pattern.
#include "FosterAST.h"

#endif // header guard

