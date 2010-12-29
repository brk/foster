// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"
#include "parse/ParsingContext.h"
#include "base/Diagnostics.h"
#include "base/Assert.h"

#include "parse/FosterUtils.h"

#include <sstream>

using std::vector;
using std::map;

using foster::SourceRange;

std::ostream& operator<<(std::ostream& out, const llvm::Type& ty) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  ss << ty;
  return out << ss.str();
}

std::string str(const llvm::Type* ty) {
  std::string s;
  llvm::raw_string_ostream ss(s);
  if (ty) { ss << *ty; } else { ss << "<NULL ty>"; }
  return ss.str();
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
      TypeAST* ret = recon(fnty->getReturnType());
      vector<TypeAST*> args;
      for (size_t i = 0; i < fnty->getNumParams(); ++i) {
         args.push_back(recon(fnty->getParamType(i)));
      }
      return FnTypeAST::get(ret, args, "fastcc");
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

// virtual
bool TypeAST::canConvertTo(TypeAST* otherType) {
  bool rv = arePhysicallyCompatible(this->getLLVMType(),
                                    otherType->getLLVMType());
  if (!rv) {
    // TODO want source range from ExprAST asking for conversion
    llvm::outs() << str(this) << "  [cannot convert to]  "
              << str(otherType) << "\n";
  }
  return rv;
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
                             freshName(name), sourceRange);
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

// virtual
bool RefTypeAST::canConvertTo(TypeAST* otherType) {
  return TypeAST::canConvertTo(otherType);
}

/////////////////////////////////////////////////////////////////////

FnTypeAST* FnTypeAST::get(TypeAST* returnType,
                          const vector<TypeAST*>& argTypes,
                          const std::string& callingConvName) {
  ASSERT(returnType) << "FnTypeAST::get() needs non-NULL return type";

  FnTypeAST* fty = new FnTypeAST(returnType,
                       argTypes,
                       callingConvName,
                       SourceRange::getEmptyRange());
  fty->getCallingConventionID(); // ensure we have a valid calling convention...
  return fty;
}

const llvm::Type* FnTypeAST::getLLVMType() const {
  if (!repr) {
    if (closedOverVars) {
      repr = genericClosureTypeFor(this)->getLLVMType();
    } else {
      repr = getLLVMFnType();
    }
  }
  return repr;
}

const llvm::FunctionType* FnTypeAST::getLLVMFnType() const {
  vector<const llvm::Type*> loweredArgTypes;
  for (size_t i = 0; i < argTypes.size(); ++i) {
    const llvm::Type* ty = argTypes[i]->getLLVMType();
    //llvm::outs() << "\tfn arg " << i << " :: " << str(ty) << "\n";
    loweredArgTypes.push_back(ty);
  }

  return llvm::FunctionType::get(returnType->getLLVMType(),
                                 loweredArgTypes,
                                 /*isVarArg=*/ false);
}

llvm::CallingConv::ID FnTypeAST::getCallingConventionID() {
  if (callingConvention == "fastcc") {
    return llvm::CallingConv::Fast;
  } else if (callingConvention == "ccc") {
    return llvm::CallingConv::C;
  } else {
    ASSERT(false) << "Unknown calling convention: " << callingConvention;
    return llvm::CallingConv::C;
  }
}

/////////////////////////////////////////////////////////////////////

const llvm::Type* TupleTypeAST::getLLVMType() const {
  if (!repr) {
    vector<const llvm::Type*> loweredTypes;
    for (size_t i = 0; i < parts.size(); ++i) {
      loweredTypes.push_back(parts[i]->getLLVMType());
    }

    repr = llvm::StructType::get(
            llvm::getGlobalContext(), loweredTypes, /*isPacked=*/false);
  }
  return repr;
}

TypeAST*& TupleTypeAST::getContainedType(size_t i) {
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

// virtual
bool CoroTypeAST::canConvertTo(TypeAST* otherType) {
  ASSERT(false) << "CoroTypeAST :: canConvertTo " << str(otherType);
  return false;
}

TypeAST*& CoroTypeAST::getContainedType(size_t i) {
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
  }
  return repr;
}

// virtual
bool CArrayTypeAST::canConvertTo(TypeAST* otherType) {
  ASSERT(false) << "CArrayTypeAST :: canConvertTo " << str(otherType);
  return false;
}

TypeAST*& CArrayTypeAST::getContainedType(size_t i) {
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

