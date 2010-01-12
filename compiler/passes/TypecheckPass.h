// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b3f24963055d7_81582449
#define H_4b3f24963055d7_81582449

#include "FosterASTVisitor.h"

struct TypecheckPass : public FosterASTVisitor {
  // typeParsingMode allows us to parse an AST as a type specification.
  // The only difference from the "main" TypecheckPass is that the type of
  // a variable is determined from its name; e.g.
  // VariableAST("i32", ...) gets type LLVMTypeFor("i32") instead of inspecting
  // the "provided" type.
  bool typeParsingMode;
  
  TypecheckPass() : typeParsingMode(false) {}
  
  #include "FosterASTVisitor.decls.inc.h"
};

#endif // header guard

