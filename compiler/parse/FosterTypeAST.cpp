// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"
#include "base/Diagnostics.h"
#include "base/Assert.h"

#include "FosterUtils.h"
#include "passes/TypecheckPass.h"

using foster::SourceRange;

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

std::map<const llvm::Type*, TypeAST*> TypeAST::thinWrappers;

static std::map<const llvm::Type*, TypeAST*> seen;

TypeAST* TypeAST::get(const llvm::Type* loweredType) {
  if (!loweredType) return NULL;

  if (loweredType->isPointerTy()) {
    if (0) std::cerr << "TypeAST::get() warning: pointer types should "
             " be passed to RefTypeAST, not base TypeAST!" << std::endl;
    const llvm::Type* pointee = loweredType->getContainedType(0);
    if (TypeAST* s = seen[pointee]) {
      if (s == (TypeAST*) 1) {
        return RefTypeAST::get(new TypeAST(pointee,
                                   SourceRange::getEmptyRange()));
      } else {
        return s;
      }
    }
    return RefTypeAST::get(TypeAST::get(pointee)); 
  }

  if (const llvm::FunctionType* fnty
         = llvm::dyn_cast<const llvm::FunctionType>(loweredType)) {
    if (0) std::cerr << "TypeAST::get() warning: function types should "
                 "not be passed to TypeAST::get()!" << std::endl;
    TypeAST* ret = TypeAST::get(fnty->getReturnType());
    std::vector<TypeAST*> args;
    for (size_t i = 0; i < fnty->getNumParams(); ++i) {
       args.push_back(TypeAST::get(fnty->getParamType(i))); 
    }
    return FnTypeAST::get(ret, args, "fastcc");
  }

  if (const llvm::StructType* sty
         = llvm::dyn_cast<const llvm::StructType>(loweredType)) {
    seen[sty] = (TypeAST*) 1;
    std::vector<TypeAST*> args;
    for (size_t i = 0; i < sty->getNumElements(); ++i) {
       args.push_back(TypeAST::get(sty->getContainedType(i))); 
    }
    return TupleTypeAST::get(args);
  }

  TypeAST* tyast = thinWrappers[loweredType];
  if (tyast) { return tyast; }
  tyast = new TypeAST(loweredType, SourceRange::getEmptyRange()); 
  thinWrappers[loweredType] = tyast;
  return tyast;
}

////////////////////////////////////////////////////////////////////

// virtual
bool TypeAST::canConvertTo(TypeAST* otherType) {
  bool rv = arePhysicallyCompatible(this->getLLVMType(),
                                    otherType->getLLVMType());
  if (!rv) {
    // TODO want source range from ExprAST asking for conversion
    std::cout << str(this) << "  [cannot convert to]  "
              << str(otherType) << std::endl;
  }
  return rv;
}

////////////////////////////////////////////////////////////////////

std::map<RefTypeAST::RefTypeArgs, RefTypeAST*> RefTypeAST::refCache;

RefTypeAST* RefTypeAST::get(TypeAST* baseType, bool nullable /* = false */) {
  ASSERT(baseType);

  RefTypeArgs args = std::make_pair(baseType, nullable);
  RefTypeAST* ref = refCache[args];
  if (ref) return ref;
  ref = new RefTypeAST(baseType, nullable, SourceRange::getEmptyRange());
  refCache[args] = ref;
  return ref;
}

// Assuming T is a non-pointer type, convert both
// (T*) and (T ) to (nullable T*).
RefTypeAST* RefTypeAST::getNullableVersionOf(TypeAST* ty) {
  ASSERT(ty) << "Can't get nullable version of NULL!";
  if (RefTypeAST* ref = dynamic_cast<RefTypeAST*>(ty)) {
    return RefTypeAST::get(ref->getElementType(), true);
  } else {
    return RefTypeAST::get(ty, true);
  }
}

// virtual
bool RefTypeAST::canConvertTo(TypeAST* otherType) {
  if (RefTypeAST* other = dynamic_cast<RefTypeAST*>(otherType)) {
    if (isNullable() && !other->isNullable()) {
      return false;
    }
  }
  return TypeAST::canConvertTo(otherType);
}

/////////////////////////////////////////////////////////////////////

FnTypeAST* FnTypeAST::get(TypeAST* returnType,
                          const std::vector<TypeAST*>& argTypes,
                          const std::string& callingConvName) {
  std::vector<const llvm::Type*> loweredArgTypes;
  for (size_t i = 0; i < argTypes.size(); ++i) {
    loweredArgTypes.push_back(argTypes[i]->getLLVMType());
  }

  return new FnTypeAST(
	    llvm::FunctionType::get(returnType->getLLVMType(),
                                    loweredArgTypes, /*isVarArg=*/ false),
                       returnType,
                       argTypes,
                       callingConvName,
                       SourceRange::getEmptyRange());
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

std::map<TupleTypeAST::Args, TupleTypeAST*> TupleTypeAST::tupleTypeCache;

TupleTypeAST* TupleTypeAST::get(const std::vector<TypeAST*>& argTypes) {
  TupleTypeAST* tup = tupleTypeCache[argTypes];
  if (tup) return tup;

  std::vector<const llvm::Type*> loweredTypes;
  for (size_t i = 0; i < argTypes.size(); ++i) {
    loweredTypes.push_back(argTypes[i]->getLLVMType());
  }
  const llvm::StructType* sty = llvm::StructType::get(
            llvm::getGlobalContext(), loweredTypes, /*isPacked=*/false);
  tup = new TupleTypeAST(sty, argTypes, SourceRange::getEmptyRange());
  tupleTypeCache[argTypes] = tup;
  return tup;
}

/////////////////////////////////////////////////////////////////////

FnTypeAST* ClosureTypeAST::getFnType() const {
  if (!fntype) {
    TypecheckPass tp; proto->accept(&tp);
    if (FnTypeAST* fnty = tryExtractCallableType(proto->type)) {
      fntype = fnty;
    }
  }
  return fntype;
}

std::ostream& ClosureTypeAST:: operator<<(std::ostream& out) const {
  return out << "ClosureTypeAST(" << str(proto->type) << ")";
}

const llvm::Type* ClosureTypeAST::getLLVMType() const {
  if (!repr) {
    clotype = genericClosureTypeFor(getFnType());
    const_cast<ClosureTypeAST*>(this)->repr = clotype->getLLVMType();
  }
  return repr;
}

// static
SimdVectorTypeAST* SimdVectorTypeAST::get(LiteralIntTypeAST* size,
                                          TypeAST* type,
                                          const SourceRange& sourceRange) {
  llvm::VectorType* vecTy = llvm::VectorType::get(type->getLLVMType(),
                                                  size->getNumericalValue());
  return new SimdVectorTypeAST(vecTy, sourceRange);
}
