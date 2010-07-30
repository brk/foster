// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_TYPE_AST_VISITOR
#define FOSTER_TYPE_AST_VISITOR

struct TypeAST;

// Forward-declare all the AST node types
#define FOSTER_AST_VISITOR_GEN(type) struct type;
#include "parse/TypeASTVisitor.decls.inc.h"
#undef  FOSTER_AST_VISITOR_GEN

struct TypeASTVisitor {
  explicit TypeASTVisitor() {}
  virtual ~TypeASTVisitor() {}

  // Declare the individual (pure virtual) visit function for the AST node types
  #define FOSTER_AST_VISITOR_PURE_VIRTUAL
  #include "parse/TypeASTVisitor.decls.inc.h"
  #undef  FOSTER_AST_VISITOR_PURE_VIRTUAL
};

// This has to be included after the declaration for FosterASTVisitor
// because the classes in FosterAST depend on these declarations for
// the double-dispatch portion of the Visitor pattern.
#include "FosterTypeAST.h"

#endif // header guard

