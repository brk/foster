// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/Assert.h"
#include "base/LLVMUtils.h"

#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"
#include "parse/FosterUtils.h"

#include "llvm/Module.h"

#include <sstream>

using std::vector;
using std::map;

using foster::EDiag;
using foster::SourceRange;

const llvm::Type* llvmIntType(int n) {
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

map<const llvm::Type*, TypeAST*> PrimitiveTypeAST::thinWrappers;

TypeAST* PrimitiveTypeAST::get(const std::string& name,
                               const llvm::Type* loweredType) {
  ASSERT(loweredType);
  TypeAST* tyast = thinWrappers[loweredType];
  if (tyast) { return tyast; }
  tyast = new PrimitiveTypeAST(name, loweredType, SourceRange::getEmptyRange());
  thinWrappers[loweredType] = tyast;
  return tyast;
}

////////////////////////////////////////////////////////////////////

const llvm::Type* NamedTypeAST::getLLVMType() const {
  ASSERT(namedType);
  if (!repr) {
    repr = namedType->getLLVMType();
  }
  ASSERT(repr) << "no named type: " << name;
  return repr;
}

////////////////////////////////////////////////////////////////////

/*
const llvm::PointerType* DataTypeAST::getOpaquePointerTy(llvm::Module* mod) const {
  if (!this->opaq) {
    EDiag() << "Generating opaque pointer for data type " << this->name;
    this->opaq = llvm::OpaqueType::get(llvm::getGlobalContext());
    if (mod) { mod->addTypeName(this->name, this->opaq); }
  }
  return llvm::PointerType::getUnqual(this->opaq);
}
*/

const llvm::Type* DataTypeAST::getLLVMType() const {
  //return this->getOpaquePointerTy(NULL);
  return llvm::PointerType::getUnqual(llvmIntType(999));
}

////////////////////////////////////////////////////////////////////

const llvm::Type* RefTypeAST::getLLVMType() const {
  if (!repr) {
    repr = llvm::PointerType::getUnqual(underlyingType->getLLVMType());
  }
  return repr;
}

map<RefTypeAST::RefTypeArgs, RefTypeAST*> RefTypeAST::refCache;

RefTypeAST* RefTypeAST::get(TypeAST* baseType) {
  ASSERT(baseType);

  RefTypeArgs args = baseType;
  RefTypeAST* ref = refCache[args];
  if (ref) return ref;
  ref = new RefTypeAST(baseType, SourceRange::getEmptyRange());
  refCache[args] = ref;
  return ref;
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

  // By default, function types are not proc types...
  if (annots["proc"] == "") {
    annots["proc"] = "false";
  }
}

const llvm::Type* FnTypeAST::getLLVMType() const {
  if (!repr) {
    if (isMarkedAsClosure()) {
      repr = genericClosureTypeFor(this)->getLLVMType();
    } else {
      repr = llvm::PointerType::getUnqual(getLLVMFnType());
    }
  }
  return repr;
}

const llvm::FunctionType* FnTypeAST::getLLVMFnType() const {
  vector<const llvm::Type*> loweredArgTypes;

  //llvm::outs() << "FnTypeAST: " << str(this) << "\n";
  for (size_t i = 0; i < argTypes.size(); ++i) {
    const llvm::Type* ty = argTypes[i]->getLLVMType();
    //llvm::outs() << "\tfn arg " << i << " :: " << str(ty) << "\n";
    loweredArgTypes.push_back(ty);
  }

  const llvm::Type* retTy = returnType->getLLVMType();

  // TODO conflict here between polymorphism (which needs
  // a uniform ABI) and C-compatibility (which says that
  // procs returning unit should be marked void?
  if (isUnit(retTy)) {
    retTy = llvm::Type::getVoidTy(llvm::getGlobalContext());
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

const llvm::Type* TupleTypeAST::getLLVMTypeUnboxed() const {
  vector<const llvm::Type*> loweredTypes;
  for (size_t i = 0; i < parts.size(); ++i) {
    loweredTypes.push_back(parts[i]->getLLVMType());
  }
  if (loweredTypes.empty()) {
    return TypeAST::i(8)->getLLVMType();
  } else {
    return llvm::StructType::get(
            llvm::getGlobalContext(), loweredTypes, /*isPacked=*/false);
  }
}

const llvm::Type* TupleTypeAST::getLLVMType() const {
  return llvm::PointerType::getUnqual(getLLVMTypeUnboxed());
}

TypeAST*& TupleTypeAST::getContainedType(int i) {
  ASSERT(indexValid(i));
  return parts[i];
}

TupleTypeAST* TupleTypeAST::get(const vector<TypeAST*>& argTypes) {
  if (!argTypes.empty()) {
    ASSERT(argTypes.back()) << "Tuple type must not contain NULL members.";
  }
  return new TupleTypeAST(argTypes, SourceRange::getEmptyRange());
}

/////////////////////////////////////////////////////////////////////

const llvm::Type* TypeTypeAppAST::getLLVMType() const {
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

const llvm::Type* CoroTypeAST::getLLVMType() const {
  if (!repr) {
    std::vector<const llvm::Type*> fieldTypes;
    fieldTypes.push_back(foster_generic_coro_t);
    fieldTypes.push_back(this->a->getLLVMType());

    repr = llvm::PointerType::getUnqual(
                llvm::StructType::get(llvm::getGlobalContext(),
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


const llvm::Type* CArrayTypeAST::getLLVMType() const {
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

const llvm::Type* ArrayTypeAST::getSizedArrayTypeRef(const llvm::Type* t, int64_t n) {
  return llvm::PointerType::getUnqual(
          llvm::StructType::get(llvm::getGlobalContext(),
                      llvm::IntegerType::get(llvm::getGlobalContext(), 64),
                      llvm::ArrayType::get(t, n),
                            NULL));
}


const llvm::Type* ArrayTypeAST::getZeroLengthTypeRef(const llvm::Type* t) {
  return getSizedArrayTypeRef(t, 0);
}

const llvm::Type* ArrayTypeAST::getLLVMType() const {
  if (!repr) {
    repr = getZeroLengthTypeRef(this->cell->getLLVMType());
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

const llvm::Type* ForallTypeAST::getLLVMType() const {
  ASSERT(false) << "No getLLVMType() for ForallTypeAST!";
  return NULL;
}
