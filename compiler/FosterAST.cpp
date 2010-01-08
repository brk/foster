// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "FosterAST.h"

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
FosterSymbolTable<const Type> typeScope;
FosterSymbolTable<ExprAST> varScope;

std::ostream& operator<<(std::ostream& out, ExprAST& expr) {
  return expr.operator<<(out);
}

/** Macros in TargetSelect.h conflict with those from ANTLR... */
void fosterLLVMInitializeNativeTarget() {
  llvm::InitializeNativeTarget();
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
  } else { // If it's a template, make the subtitution, even the first time
    ss << curr; // int>string
    like.replace(pos, pos+2, ss.str());
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

const Type* LLVMTypeFor(const string& name) { return module->getTypeByName(name); }

void initModuleTypeNames() {
  module->addTypeName("i32", llvm::IntegerType::get(getGlobalContext(), 32));
  module->addTypeName("i1", llvm::IntegerType::get(getGlobalContext(), 1));
  
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

llvm::Constant* IntAST::getConstantValue() {
  return ConstantInt::get(this->type, APInt(32u, Clean, Base));
}

