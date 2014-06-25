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

using std::vector;
using std::map;

using foster::EDiag;
using foster::SourceRange;

llvm::Type* foster_generic_coro_t = NULL;
TypeAST* foster_generic_coro_ast  = NULL;

TypeAST* getGenericClosureEnvType() { return RefTypeAST::get(TypeAST::i(8)); }
RefTypeAST* getUnitType() {
  std::vector<TypeAST*> argTypes;
  return RefTypeAST::get(StructTypeAST::get(argTypes));
}

llvm::Type* llvmIntType(int n) {
  return llvm::IntegerType::get(llvm::getGlobalContext(), n);
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
  ASSERT(!llvm::isa<llvm::StructType>(loweredType)) << str(loweredType);
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
  llvm::StructType* dt_opaque_named_ty =
         llvm::StructType::create(llvm::getGlobalContext(),
                                               std::string(this->name + ".DT"));
  return llvm::PointerType::getUnqual(dt_opaque_named_ty);
}

////////////////////////////////////////////////////////////////////

llvm::Type* RefTypeAST::getLLVMType() const {
  if (!repr) {
    repr = llvm::PointerType::getUnqual(underlyingType->getLLVMType());
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
                     ValAbs* precond,
                     std::map<string, string> _annots)
    : TypeAST("FnType", NULL, SourceRange::getEmptyRange()),
      returnType(returnType),
      argTypes(argTypes),
      precond(precond),
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
    repr = llvm::PointerType::getUnqual(getLLVMFnType());
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

  // TODO conflict here between polymorphism (which needs
  // a uniform ABI) and C-compatibility (which says that
  // procs returning unit should be marked void?
  if (typesEq(retTy, getUnitType()->getLLVMType())) {
    retTy = llvm::Type::getVoidTy(retTy->getContext());
  }

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

llvm::Type* TupleTypeAST::getLLVMType() const {
  ASSERT(false) << "TupleTypeAST should not be used by the backend!";
  return NULL;
}

TupleTypeAST* TupleTypeAST::get(const vector<TypeAST*>& argTypes) {
  if (!argTypes.empty()) {
    ASSERT(argTypes.back()) << "Tuple type must not contain NULL members.";
  }
  return new TupleTypeAST(argTypes, SourceRange::getEmptyRange());
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////

StructTypeAST::StructTypeAST(std::string name, const SourceRange& sourceRange)
  : IndexableTypeAST("StructType", NULL, sourceRange) {
  repr = llvm::StructType::create(llvm::getGlobalContext(), name);
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

llvm::Type* StructTypeAST::getLLVMType() const {
  if (repr) return repr;
  repr = llvm::StructType::get(llvm::getGlobalContext(), getLoweredTypes());
  return repr;
}

TypeAST*& StructTypeAST::getContainedType(int i) {
  ASSERT(indexValid(i));
  return parts[i];
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

llvm::Type* TypeTypeAppAST::getLLVMType() const {
  ASSERT(false) << "TypeTypeAppAST::getLLVMType()";
  return NULL;
}

TypeAST*& TypeTypeAppAST::getContainedType(int i) {
  ASSERT(indexValid(i));
  return parts[i];
}

TypeTypeAppAST* TypeTypeAppAST::get(const vector<TypeAST*>& argTypes) {
  ASSERT(argTypes.size() >= 2) << "TypeTypeAppAST must contain at least two types.";
  return new TypeTypeAppAST(argTypes, SourceRange::getEmptyRange());
}

/////////////////////////////////////////////////////////////////////

llvm::Type* CoroTypeAST::getLLVMType() const {
  if (!repr) {
    std::vector<llvm::Type*> fieldTypes;
    fieldTypes.push_back(foster_generic_coro_t);
    fieldTypes.push_back(this->a->getLLVMType());

    repr = llvm::PointerType::getUnqual(
                llvm::StructType::get(fieldTypes.back()->getContext(),
                                 fieldTypes, /*isPacked=*/false));
  }
  return repr;
}

TypeAST*& CoroTypeAST::getContainedType(int i) {
  ASSERT(i >= 0 && i < getNumContainedTypes());
  return (i == 0) ? a : b;
}

CoroTypeAST* CoroTypeAST::get(TypeAST* targ, TypeAST* tret) {
  ASSERT(targ);
  ASSERT(tret);
  return new CoroTypeAST(targ, tret, SourceRange::getEmptyRange());
}

/////////////////////////////////////////////////////////////////////


llvm::Type* CArrayTypeAST::getLLVMType() const {
  if (!repr) {
    ASSERT(false);
  }
  return repr;
}

TypeAST*& CArrayTypeAST::getContainedType(int i) {
  ASSERT(i >= 0 && i < getNumContainedTypes());
  return cell;
}

CArrayTypeAST* CArrayTypeAST::get(TypeAST* tcell, uint64_t size) {
  ASSERT(tcell);
  ASSERT(int64_t(size) >= 0LL)
    << "either you tried creating a buffer of "
    << "more than 16 million terabytes, or the size "
    << "that reached CArrayTypeAST::get() was negative.";
  return new CArrayTypeAST(tcell, size, SourceRange::getEmptyRange());
}


/////////////////////////////////////////////////////////////////////

llvm::Type* ArrayTypeAST::getSizedArrayTypeRef(llvm::Type* t, int64_t n) {
  std::vector<llvm::Type*> structElemTypes;
  // embedded length
  structElemTypes.push_back(llvm::IntegerType::get(t->getContext(), 64));
  structElemTypes.push_back(llvm::ArrayType::get(t, n));
  return llvm::PointerType::getUnqual(
          llvm::StructType::get(t->getContext(),
                                llvm::makeArrayRef(structElemTypes)));
}


llvm::Type* ArrayTypeAST::getZeroLengthTypeRef(TypeAST* t) {
  return getSizedArrayTypeRef(t->getLLVMType(), 0);
}

llvm::Type* ArrayTypeAST::getLLVMType() const {
  if (!repr) {
    repr = getZeroLengthTypeRef(this->cell);
  }
  return repr;
}

TypeAST*& ArrayTypeAST::getContainedType(int i) {
  ASSERT(i >= 0 && i < getNumContainedTypes());
  return cell;
}

ArrayTypeAST* ArrayTypeAST::get(TypeAST* tcell) {
  ASSERT(tcell);
  return new ArrayTypeAST(tcell, SourceRange::getEmptyRange());
}

/////////////////////////////////////////////////////////////////////

llvm::Type* ForallTypeAST::getLLVMType() const {
  ASSERT(false) << "No getLLVMType() for ForallTypeAST!";
  return NULL;
}
