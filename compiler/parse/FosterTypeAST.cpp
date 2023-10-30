// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/Assert.h"
#include "base/LLVMUtils.h"

#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"

#include "llvm/IR/Module.h"

#include <sstream>
#include <string>

using std::string;
using std::vector;
using std::map;

using foster::EDiag;
using foster::SourceRange;
using foster::fosterLLVMContext;

llvm::Type* foster_generic_coro_t = NULL;
llvm::Type* foster_generic_split_coro_ty = NULL;
StructTypeAST* foster_generic_coro_ast  = NULL;

TypeAST* getGenericClosureEnvType() { return RefTypeAST::get(TypeAST::i(8)); }
RefTypeAST* getUnitType() {
  std::vector<TypeAST*> argTypes;
  return RefTypeAST::get(StructTypeAST::get(argTypes));
}

llvm::Type* llvmIntType(int n) {
  return llvm::IntegerType::get(fosterLLVMContext, n);
}

/////////////////////////////////////////////////////////////////////

//virtual
TypeAST::~TypeAST() {}

TypeAST* TypeAST::i(int n) {
  std::stringstream ss; ss << "i" << n;
  return PrimitiveTypeAST::get(ss.str(), llvmIntType(n));
}

////////////////////////////////////////////////////////////////////

map<llvm::Type*, TypeAST*> PrimitiveTypeAST::thinWrappers;

TypeAST* PrimitiveTypeAST::get(const std::string& name,
                               llvm::Type* loweredType) {
  ASSERT(loweredType);
  //ASSERT(!llvm::isa<llvm::StructType>(loweredType)) << str(loweredType);
  TypeAST* tyast = thinWrappers[loweredType];
  if (tyast) { return tyast; }
  tyast = new PrimitiveTypeAST(name, loweredType, SourceRange::getEmptyRange());
  thinWrappers[loweredType] = tyast;
  return tyast;
}

////////////////////////////////////////////////////////////////////

llvm::Type* NamedTypeAST::getLLVMType() const {
  ASSERT(namedType);
  if (!repr) {
    repr = namedType->getLLVMType();
  }
  ASSERT(repr) << "no named type: " << name;
  return repr;
}

////////////////////////////////////////////////////////////////////

llvm::Type* DataTypeAST::getLLVMType() const {
  if (this->name == "CVoid") {
    return foster::builder.getVoidTy();
  }
  return foster::builder.getPtrTy();
}

////////////////////////////////////////////////////////////////////

llvm::Type* RefTypeAST::getLLVMType() const {
  if (!repr) {
    repr = foster::builder.getPtrTy();
  }
  return repr;
}

RefTypeAST* RefTypeAST::get(TypeAST* baseType) {
  ASSERT(baseType);
  return new RefTypeAST(baseType, SourceRange::getEmptyRange());
}

/////////////////////////////////////////////////////////////////////

FnTypeAST::FnTypeAST(TypeAST* returnType,
                     const std::vector<TypeAST*>& argTypes,
                     std::map<string, string> _annots)
    : TypeAST("FnType", NULL, SourceRange::getEmptyRange()),
      returnType(returnType),
      argTypes(argTypes),
      annots(_annots) {
  ASSERT(returnType) << "FnTypeAST() needs non-NULL return type";
  getCallingConventionID(); // ensure we have a valid calling convention...

  // By default, function types are not proc types (at the front-end).
  if (annots["proc"] == "") {
    annots["proc"] = "false";
  }
}

llvm::Type* FnTypeAST::getLLVMType() const {
  if (!repr) { // At the backend, FnTypeAST == LLProcType
    repr = rawPtrTo(getLLVMFnType());
  }
  return repr;
}

llvm::FunctionType* FnTypeAST::getLLVMFnType() const {
  vector<llvm::Type*> loweredArgTypes;

  //llvm::outs() << "FnTypeAST: " << str(this) << "\n";
  for (size_t i = 0; i < argTypes.size(); ++i) {
    llvm::Type* ty = argTypes[i]->getLLVMType();
    //llvm::outs() << "\tfn arg " << i << " :: " << str(ty) << "\n";
    loweredArgTypes.push_back(ty);
  }

  llvm::Type* retTy = returnType->getLLVMType();
  return llvm::FunctionType::get(retTy,
                                 loweredArgTypes,
                                 /*isVarArg=*/ false);
}

bool FnTypeAST::isMarkedAsClosure() const {
  std::map<std::string, std::string>::const_iterator
    it = annots.find("proc");
  ASSERT(it != annots.end()) << "FnTypeAST missing 'proc' annotation";
  return (*it).second == "false";
}

std::string FnTypeAST::getCallingConventionName() const {
  std::map<std::string, std::string>::const_iterator
    it = annots.find("callconv");
  ASSERT(it != annots.end()) << "FnTypeAST missing 'callconv' annotation";
  return (*it).second;
}

llvm::CallingConv::ID FnTypeAST::getCallingConventionID() const {
  std::string cc = getCallingConventionName();
  if (cc == "fastcc") {
    return llvm::CallingConv::Fast;
  } else if (cc == "ccc") {
    return llvm::CallingConv::C;
  } else if (cc == "coldcc") {
    return llvm::CallingConv::Cold;
  } else {
    ASSERT(false) << "Unknown calling convention: " << cc;
    return llvm::CallingConv::C;
  }
}

/////////////////////////////////////////////////////////////////////

StructTypeAST::StructTypeAST(std::string name, const SourceRange& sourceRange)
  : IndexableTypeAST("StructType", NULL, sourceRange) {
  repr = llvm::StructType::create(fosterLLVMContext, name);
}

vector<llvm::Type*> StructTypeAST::getLoweredTypes() const {
  vector<llvm::Type*> loweredTypes;
  for (size_t i = 0; i < parts.size(); ++i) {
    loweredTypes.push_back(parts[i]->getLLVMType());
  }
  return loweredTypes;
}

void StructTypeAST::setBody(const vector<TypeAST*>& argTypes) {
  parts = argTypes;
  llvm::StructType* sty = llvm::dyn_cast<llvm::StructType>(repr);
  ASSERT(sty);
  sty->setBody(getLoweredTypes());
}

llvm::StructType* StructTypeAST::getLLVMStructType() const {
  if (repr) return llvm::dyn_cast<llvm::StructType>(repr);
  auto sty = llvm::StructType::get(fosterLLVMContext, getLoweredTypes());
  repr = sty;
  return sty;
}

llvm::Type* StructTypeAST::getLLVMType() const {
  return getLLVMStructType();
}

TypeAST*& StructTypeAST::getContainedType(int i) {
  return parts.at(i);
}

StructTypeAST* StructTypeAST::get(const vector<TypeAST*>& argTypes) {
  if (!argTypes.empty()) {
    ASSERT(argTypes.back()) << "Struct type must not contain NULL members.";
  }
  return new StructTypeAST(argTypes, SourceRange::getEmptyRange());
}

StructTypeAST* StructTypeAST::getRecursive(std::string name) {
  return new StructTypeAST(name, SourceRange::getEmptyRange());
}

/////////////////////////////////////////////////////////////////////

// Returns {i64, [t, n]}
llvm::StructType* ArrayTypeAST::getSizedArrayType(llvm::Type* t, int64_t n) {
  return llvm::StructType::get(t->getContext(),
            { llvm::IntegerType::get(t->getContext(), 64)
            , llvm::ArrayType::get(t, n) });
}


llvm::StructType* ArrayTypeAST::getZeroLengthType(TypeAST* t) {
  return getSizedArrayType(t->getLLVMType(), 0);
}

llvm::Type* ArrayTypeAST::getLLVMType() const {
  if (!repr) {
    repr = getZeroLengthType(this->cell);
  }
  return llvm::PointerType::getUnqual(repr);
}

TypeAST*& ArrayTypeAST::getContainedType(int i) {
  ASSERT(i >= 0 && i < getNumContainedTypes());
  return cell;
}

ArrayTypeAST* ArrayTypeAST::get(TypeAST* tcell) {
  ASSERT(tcell);
  return new ArrayTypeAST(tcell, SourceRange::getEmptyRange());
}