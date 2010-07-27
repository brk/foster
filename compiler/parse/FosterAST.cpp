// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "parse/FosterAST.h"
#include "passes/TypecheckPass.h"
#include "FosterUtils.h"

#include "CompilationContext.h"

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
  return type.operator<<(out);
}

std::ostream& operator<<(std::ostream& out, ExprAST& expr) {
  return expr.operator<<(out);
}

/// Generates a unique name given a template; each template gets a separate
/// sequence of uniquifying numbers either embedded or appended.
string freshName(string like) {
  static std::map<string, int> counts;
  std::stringstream ss;
  size_t pos = like.find("%d", 0);
  int curr = counts[like]++;
  if (string::npos == pos) { // append uniquifier, if any
    if (curr == 0) {
      ss << like; // Only append integer when we see second copy of symbol
    } else {
      ss << like << curr;
    }
  } else { // If it's a template, make the substitution, even the first time
    ss << curr; // int>string
    like.replace(pos, 2, ss.str());
    ss.str("");
    ss.clear(); // reset
    ss << like;
  }
  return ss.str();
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

std::map<string, const Type*> builtinTypes;

TypeAST*    TypeASTFor(const string& name) {
  if (builtinTypes.count(name) == 1) {
    return TypeAST::get(builtinTypes[name]);
  } else if (TypeAST* ty = gTypeScope.lookup(name, "")) {
    return ty;
  } else {
    const Type* ty = LLVMTypeFor(name);
    if (ty) {
      std::cerr << "WARNING: have LLVMTypeFor("<<name<<")"
                << " but no TypeASTFor(...)" << std::endl;
    }
    return NULL;
  }
}

const Type* LLVMTypeFor(const string& name) {
  if (builtinTypes.count(name) == 1) {
    return builtinTypes[name];
  } else {
    return foster::module->getTypeByName(name);
  }
}

void initModuleTypeNames() {
  builtinTypes["i1"] = llvm::IntegerType::get(getGlobalContext(), 1);
  builtinTypes["i8"] = llvm::IntegerType::get(getGlobalContext(), 8);
  builtinTypes["i16"] = llvm::IntegerType::get(getGlobalContext(), 16);
  builtinTypes["i32"] = llvm::IntegerType::get(getGlobalContext(), 32);
  builtinTypes["i64"] = llvm::IntegerType::get(getGlobalContext(), 64);
  
  builtinTypes["i8*"] = llvm::PointerType::getUnqual(builtinTypes["i8"]);
  builtinTypes["i8**"] = llvm::PointerType::getUnqual(builtinTypes["i8*"]);
}

void FosterASTVisitor::visitChildren(ExprAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      this->onVisitChild(ast, ast->parts[i]);
    } else {
      EDiag() << "visitChildren saw null part " << i << " for ast node " << str(ast) << show(ast);
    }
  }
}

void FosterASTVisitor::onVisitChild(ExprAST* ast, ExprAST* child) {
  child->accept(this);
}

IntAST* literalIntAST(int lit) {
  std::stringstream ss; ss << lit;
  string text = ss.str();
  IntAST* rv = new IntAST(text, text, foster::SourceRange::getEmptyRange(), 10);
  // Assign the proper (smallest) int type to the literal
  { TypecheckPass tc; rv->accept(&tc); }
  return rv;
}

llvm::APInt IntAST::getAPInt() {
  ASSERT(this->type && this->type->getLLVMType());

  return APInt(this->type->getLLVMType()->getScalarSizeInBits(),
               Clean, Base);
}

llvm::Constant* IntAST::getConstantValue() {
  ASSERT(this->type && this->type->getLLVMType());

  return ConstantInt::get(this->type->getLLVMType(), this->getAPInt());
}

bool RefExprAST::isIndirect() {
  if (isIndirect_) return true;
  return (type && value &&
          isPointerToType(value->getType(), type->getLLVMType()));
}
