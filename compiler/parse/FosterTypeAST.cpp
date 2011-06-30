// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/Assert.h"
#include "base/LLVMUtils.h"

#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"
#include "parse/ParsingContext.h"
#include "parse/FosterUtils.h"

#include <sstream>

using std::vector;
using std::map;

using foster::SourceRange;
using foster::ParsingContext;

const char* getDefaultCallingConvRecon() {
  //foster::EDiag() << "getDefaultCallingConvRecon()";
  return foster::kDefaultFnLiteralCallingConvention;
}

bool hasEqualRepr(TypeAST* src, TypeAST* dst) {
  return src->getLLVMType() == dst->getLLVMType();
}

const llvm::Type* llvmIntType(int n) {
  return llvm::IntegerType::get(llvm::getGlobalContext(), n);
}

bool isAutoConvertible(const llvm::Type* fromTy,
                       const llvm::Type* toTy) {
  // no case for i1 needed because equality is taken care of

  bool to8  = toTy == llvmIntType(8);
  bool to16 = toTy == llvmIntType(16);
  bool to32 = toTy == llvmIntType(32);
  bool to64 = toTy == llvmIntType(64);

  if (fromTy == llvmIntType(1)) {
    return /**/ to8 /*|| to16 || to32 || to64*/;
  } else if (fromTy == llvmIntType(8)) {
    return /*to8 ||*/ to16 || to32 || to64;
  } else if (fromTy == llvmIntType(16)) {
    return /*to8 || to16 ||*/ to32 || to64;
  } else if (fromTy == llvmIntType(32)) {
    return /*to8 || to16 || to32 ||*/ to64;
  }
  // 64 bits:
  return false;
}

bool arePhysicallyCompatible(const llvm::Type* src,
                             const llvm::Type* dst) {
  return src == dst || isAutoConvertible(src, dst);
}

/////////////////////////////////////////////////////////////////////

//virtual
TypeAST::~TypeAST() {}

TypeAST* TypeAST::i(int n) {
  std::stringstream ss; ss << "i" << n;
  return NamedTypeAST::get(ss.str(), llvmIntType(n));
}

TypeAST* TypeAST::getVoid() {
  return NamedTypeAST::get("void", llvm::Type::getVoidTy(llvm::getGlobalContext()));
}

struct TypeReconstructor {
  TypeAST* recon(const llvm::Type* loweredType) {
    if (loweredType->isVoidTy()) { return TypeAST::getVoid(); }

    if (loweredType->isPointerTy()) {
      const llvm::Type* pointee = loweredType->getContainedType(0);
      if (TypeAST* s = seen[pointee]) {
        if (s == (TypeAST*) 1 && !llvm::isa<llvm::StructType>(pointee)) {
          llvm::outs() << "Recursive type: " << str(loweredType) << "\n";
          return RefTypeAST::get(NamedTypeAST::get("bogus/opaque!", pointee));
        } else {
          return s;
        }
      }
      return RefTypeAST::get(recon(pointee));
    }

    if (const llvm::FunctionType* fnty
           = llvm::dyn_cast<const llvm::FunctionType>(loweredType)) {
      ASSERT(false) << "cannot reconstruct function type " << str(fnty) << "\n";
    /*
      TypeAST* ret = recon(fnty->getReturnType());
      vector<TypeAST*> args;
      for (size_t i = 0; i < fnty->getNumParams(); ++i) {
         args.push_back(recon(fnty->getParamType(i)));
      }
      return new FnTypeAST(ret, args, getDefaultCallingConvRecon());
      */
    }

    if (const llvm::StructType* sty
           = llvm::dyn_cast<const llvm::StructType>(loweredType)) {
      seen[sty] = (TypeAST*) 1;
      vector<TypeAST*> args;
      for (size_t i = 0; i < sty->getNumElements(); ++i) {
         args.push_back(recon(sty->getContainedType(i)));
      }
      seen[sty] = (TypeAST*) 0;
      return TupleTypeAST::get(args);
    }

    if (loweredType->isArrayTy()) {
      const llvm::ArrayType* arr =
          llvm::dyn_cast<llvm::ArrayType>(loweredType);
      return CArrayTypeAST::get(
          recon(arr->getElementType()),
          arr->getNumElements());
    }

    if (llvm::dyn_cast<const llvm::OpaqueType>(loweredType)) {
      return NamedTypeAST::get("opaque", loweredType);
    }

    if (loweredType->isIntegerTy()) {
      return NamedTypeAST::get(str(loweredType), loweredType);
    }

    llvm::outs() << "TypeReconstructor::reconstruct() did not recognize " << str(loweredType) << "\n";

    return NamedTypeAST::get(str(loweredType), loweredType);
  }

  map<const llvm::Type*, TypeAST*> seen;
};

TypeAST* TypeAST::reconstruct(const llvm::Type* loweredType) {
  TypeReconstructor tr; return tr.recon(loweredType);
}

////////////////////////////////////////////////////////////////////

map<const llvm::Type*, TypeAST*> NamedTypeAST::thinWrappers;

TypeAST* NamedTypeAST::get(const std::string& name,
                           const llvm::Type* loweredType) {
  if (!loweredType) return NULL;
  if (const llvm::DerivedType* derived
                       = llvm::dyn_cast<const llvm::DerivedType>(loweredType)) {
    if (llvm::dyn_cast<const llvm::IntegerType>(loweredType)) {
      // fall through to non-derived case
    } else if (name == "opaque") {
      // fall through to non-derived case
    } else {
      llvm::errs() << "NamedTypeAST::get() warning: derived types should "
                   " not be passed to NamedTypeAST::get(" << name << ")! Got: "
                << str(loweredType) << "\n";
      return TypeAST::reconstruct(derived);
    }
  }

  TypeAST* tyast = thinWrappers[loweredType];
  if (tyast) { return tyast; }
  tyast = new NamedTypeAST(name, loweredType, SourceRange::getEmptyRange());
  thinWrappers[loweredType] = tyast;
  return tyast;
}

const llvm::Type* NamedTypeAST::getLLVMType() const {
  ASSERT(nonLLVMType || repr);
  if (!repr) {
    repr = nonLLVMType->getLLVMType();
  }
  return repr;
}

////////////////////////////////////////////////////////////////////

TypeVariableAST* TypeVariableAST::get(const std::string& name,
                                      const SourceRange& sourceRange) {
  return new TypeVariableAST(llvm::OpaqueType::get(llvm::getGlobalContext()),
                             ParsingContext::freshName(name), sourceRange);
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

const llvm::StructType* TupleTypeAST::getLLVMTypeUnboxed() const {
  vector<const llvm::Type*> loweredTypes;
  for (size_t i = 0; i < parts.size(); ++i) {
    loweredTypes.push_back(parts[i]->getLLVMType());
  }

  return llvm::StructType::get(
            llvm::getGlobalContext(), loweredTypes, /*isPacked=*/false);
}

const llvm::Type* TupleTypeAST::getLLVMType() const {
  if (!repr) {
    repr = llvm::PointerType::getUnqual(getLLVMTypeUnboxed());
  }
  return repr;
}

TypeAST*& TupleTypeAST::getContainedType(int i) {
  ASSERT(indexValid(i));
  return parts[i];
}

map<TupleTypeAST::Args, TupleTypeAST*> TupleTypeAST::tupleTypeCache;

TupleTypeAST* TupleTypeAST::get(const vector<TypeAST*>& argTypes) {
  TupleTypeAST* tup = tupleTypeCache[argTypes];
  if (!tup) {
    if (!argTypes.empty() && !argTypes.back()) {
      ASSERT(argTypes.back()) << "Tuple type must not contain NULL members.";
    }
    tup = new TupleTypeAST(argTypes, SourceRange::getEmptyRange());
    tupleTypeCache[argTypes] = tup;
  }
  return tup;
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
