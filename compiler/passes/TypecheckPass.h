// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_TYPECHECK
#define FOSTER_PASSES_TYPECHECK

#include "parse/FosterASTVisitor.h"
#include <string>

struct TypecheckPass : public FosterASTVisitor {
  // typeParsingMode allows us to parse an AST as a type specification.
  // The only difference from the "main" TypecheckPass is that the type of
  // a variable is determined from its name; e.g.
  // VariableAST("i32", ...) gets type LLVMTypeFor("i32") instead of inspecting
  // the "provided" type.
  bool typeParsingMode;
  
  TypecheckPass() : typeParsingMode(false) {}
  
  #include "parse/FosterASTVisitor.decls.inc.h"
};

inline bool isPrintRef(const ExprAST* base) {
  if (const VariableAST* var = dynamic_cast<const VariableAST*>(base)) {
    if (var->name == "print_ref") {
      return true;
    }
  }
  return false;
}

inline bool isArithOp(const std::string& op) {
  return op == "+" || op == "-" || op == "/" || op == "*";
}

inline bool isCmpOp(const std::string& op) {
  return op == "<" || op == "<=" || op == ">" || op == ">="
      || op == "==" || op == "!=";
}


#endif // header guard

