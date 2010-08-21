// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/FreshNameGenerator.h"
#include "parse/FosterAST.h"
#include "parse/CompilationContext.h"
#include "parse/ANTLRtoFosterAST.h" // just for parseAPIntFromClean()
#include "parse/FosterUtils.h"
#include "passes/PrettyPrintPass.h"

#include <map>
#include <vector>
#include <sstream>

using foster::EDiag;
using foster::show;
using foster::SourceRange;
using foster::SourceRangeHighlighter;
using foster::SourceLocation;

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::getGlobalContext;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;

using std::vector;
using std::string;

std::ostream& operator<<(std::ostream& out, TypeAST& type) {
  foster::prettyPrintType(&type, out, 40);
  return out;
}

std::ostream& operator<<(std::ostream& out, ExprAST& expr) {
  return expr.operator<<(out);
}


string str(ExprAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

string str(TypeAST* expr) {
  if (expr) {
    std::stringstream ss; ss << (*expr); return ss.str();
  } else { return "<nil>"; }
}

string str(Value* value) {
  if (value) {
    std::string s;
    llvm::raw_string_ostream ss(s); ss << *value; return ss.str();
  } else { return "<nil>"; }
}

namespace foster {

SourceRangeHighlighter show(ExprAST* ast) {
  if (!ast) {
    SourceLocation empty = SourceLocation::getInvalidLocation();
    return SourceRangeHighlighter(SourceRange(NULL, empty, empty), empty);
  }
  return show(ast->sourceRange);
}

} // namespace foster

void ExprASTVisitor::visitChildren(ExprAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      this->onVisitChild(ast, ast->parts[i]);
    } else {
      EDiag() << "visitChildren saw null part " << i << " for ast node " << str(ast) << show(ast);
    }
  }
}

void ExprASTVisitor::onVisitChild(ExprAST* ast, ExprAST* child) {
  child->accept(this);
}

IntAST* literalIntAST(int lit, const foster::SourceRange& sourceRange) {
  std::stringstream ss; ss << lit;
  string text = ss.str();
  
  APInt* p = foster::parseAPIntFromClean(text, 10, sourceRange);
  IntAST* rv = new IntAST(p->getActiveBits(), text, text, 10, sourceRange);
  return rv;
}

llvm::APInt IntAST::getAPInt() const { return *apint; }
std::string IntAST::getOriginalText() const { return text; }


llvm::Constant* IntAST::getConstantValue() const {
  ASSERT(this->type && this->type->getLLVMType());

  return ConstantInt::get(this->type->getLLVMType(), this->getAPInt());
}

bool RefExprAST::isIndirect() {
  if (isIndirect_) return true;
  return (type && value &&
          isPointerToType(value->getType(), type->getLLVMType()));
}
