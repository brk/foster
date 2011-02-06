// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_DUMPTOPROTOBUF
#define FOSTER_PASSES_DUMPTOPROTOBUF

#include "parse/ExprASTVisitor.h"
#include "parse/TypeASTVisitor.h"

#include "_generated_/FosterAST.pb.h"

struct DumpToProtobufPass : public ExprASTVisitor {
  foster::fepb::Expr* current;

  DumpToProtobufPass(foster::fepb::Expr* current) : current(current) {}

  virtual void visitChildren(ExprAST* ast) {
    // Only visit children manually!
  }

  #include "parse/ExprASTVisitor.decls.inc.h"
};


struct DumpTypeToProtobufPass : public TypeASTVisitor {
  foster::fepb::Type* current;

  DumpTypeToProtobufPass(foster::fepb::Type* current) : current(current) {}

  virtual void visitChildren(TypeAST* ast) {
    // Only visit children manually!
  }

  #include "parse/TypeASTVisitor.decls.inc.h"
};


#endif // header guard

