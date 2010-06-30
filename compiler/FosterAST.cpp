// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "FosterAST.h"
#include "TypecheckPass.h"
#include "FosterUtils.h"

#include "llvm/Target/TargetSelect.h"
#include "llvm/Module.h"

#include <map>
#include <vector>
#include <sstream>

using llvm::Type;
using llvm::BasicBlock;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;

using std::vector;
using std::string;

llvm::ExecutionEngine* ee;
llvm::IRBuilder<> builder(getGlobalContext());
llvm::Module* module;

FosterSymbolTable<Value> scope;
FosterSymbolTable<TypeAST> typeScope;
FosterSymbolTable<ExprAST> varScope;

std::ostream& operator<<(std::ostream& out, TypeAST& type) {
  return type.operator<<(out);
}

std::ostream& operator<<(std::ostream& out, ExprAST& expr) {
  return expr.operator<<(out);
}

/** Macros in TargetSelect.h conflict with those from ANTLR... */
void fosterInitializeLLVM() {
  llvm::InitializeNativeTarget();

  // Initializing the native target doesn't initialize the native
  // target's ASM printer, so we have to do it ourselves.
#if LLVM_NATIVE_ARCH == X86Target
  LLVMInitializeX86AsmPrinter();
#else
  std::cerr << "Warning: not initializing any asm printer!" << std::endl;
#endif

}

/// Generates a unique name given a template; each template gets a separate
/// sequence of uniquifying numbers either embedded or appended.
string freshName(string like) {
  static std::map<string, int> counts;
  std::stringstream ss;
  int pos = like.find("%d", 0);
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

string join(string glue, Exprs args) {
  std::stringstream ss;
  if (args.size() > 0) {
    if (args[0]) {
      ss << *args[0];
    } else {
      ss << "<nil>";
    }
    for (int i = 1; i < args.size(); ++i) {
      ss << glue;
      if (args[i]) {
        ss << *args[i];
      } else {
        ss << "<nil>";
      }
    }
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

std::map<string, const Type*> builtinTypes;

TypeAST*    TypeASTFor(const string& name) {
  if (builtinTypes.count(name) == 1) {
    return TypeAST::get(builtinTypes[name]);
  } else if (TypeAST* ty = typeScope.lookup(name, "")) {
    return ty;
  } else {
    const Type* ty = LLVMTypeFor(name);
    if (ty) {
      std::cerr << "WARNING: LLVMTypeFor("<<name<<") > TypeASTFor(...)" << std::endl;
    }
    return NULL;
  }
}

const Type* LLVMTypeFor(const string& name) {
  if (builtinTypes.count(name) == 1) {
    return builtinTypes[name];
  } else {
    return module->getTypeByName(name);
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

  /*
  std::vector<const Type*> StringParts;
  StringParts.push_back(Type::Int32Ty);
  StringParts.push_back(PointerType::get(Type::Int8Ty, DEFAULT_ADDRESS_SPACE));
  module->addTypeName("String", StructType::get(StringParts));
  */

  //const unsigned DEFAULT_ADDRESS_SPACE = 0u;
  //module->addTypeName("String",
  //  llvm::PointerType::get(Type::getInt8Ty(gcon), DEFAULT_ADDRESS_SPACE));
}

void FosterASTVisitor::visitChildren(ExprAST* ast) {
  for (int i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      this->onVisitChild(ast, ast->parts[i]);
    } else {
      std::cerr << "visitChildren saw null part " << i << " for ast node " << (*ast) << std::endl;
    }
  }
}

void FosterASTVisitor::onVisitChild(ExprAST* ast, ExprAST* child) {
  child->accept(this);
}

IntAST* literalIntAST(int lit) {
  std::stringstream ss; ss << lit;
  IntAST* rv = new IntAST(string(ss.str()), string(ss.str()), 10);
  // Assign the proper (smallest) int type to the literal
  { TypecheckPass tc; rv->accept(&tc); }
  return rv;
}

llvm::APInt IntAST::getAPInt() {
  return APInt(this->type->getLLVMType()->getScalarSizeInBits(),
               Clean, Base);
}

llvm::Constant* IntAST::getConstantValue() {
  return ConstantInt::get(this->type->getLLVMType(), this->getAPInt());
}

bool RefExprAST::isIndirect() {
  return isIndirect_ || (type && value && isPointerToType(value->getType(), type->getLLVMType()));
}
