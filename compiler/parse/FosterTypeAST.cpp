// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"
#include "base/Diagnostics.h"
#include "base/Assert.h"

#include "FosterUtils.h"
#include "passes/TypecheckPass.h"

using std::vector;
using std::map;

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

map<const llvm::Type*, TypeAST*> TypeAST::thinWrappers;

static map<const llvm::Type*, TypeAST*> seen;

TypeAST* TypeAST::i(int n) { return TypeAST::get(llvmIntType(n)); }

TypeAST* TypeAST::getVoid() {
  return TypeAST::get(llvm::Type::getVoidTy(llvm::getGlobalContext()));
}

TypeAST* TypeAST::get(const llvm::Type* loweredType) {
  if (!loweredType) return NULL;
  if (const llvm::DerivedType* derived
                       = llvm::dyn_cast<const llvm::DerivedType>(loweredType)) {
    if (llvm::dyn_cast<const llvm::IntegerType>(loweredType)) {
      // fall through to non-derived case
    } else {
      std::cerr << "TypeAST::get() warning: derived types should "
                   " not be passed to TypeAST::get()! Got: "
                << str(loweredType) << std::endl;
      return TypeAST::reconstruct(derived);
    }
  }
  
  TypeAST* tyast = thinWrappers[loweredType];
  if (tyast) { return tyast; }
  tyast = new TypeAST(loweredType, SourceRange::getEmptyRange()); 
  thinWrappers[loweredType] = tyast;
  return tyast;
}

TypeAST* TypeAST::reconstruct(const llvm::Type* loweredType) {
  if (loweredType->isPointerTy()) {
    const llvm::Type* pointee = loweredType->getContainedType(0);
    if (TypeAST* s = seen[pointee]) {
      if (s == (TypeAST*) 1) {
        return RefTypeAST::get(new TypeAST(pointee,
                                   SourceRange::getEmptyRange()));
      } else {
        return s;
      }
    }
    return RefTypeAST::get(TypeAST::reconstruct(pointee)); 
  }

  if (const llvm::FunctionType* fnty
         = llvm::dyn_cast<const llvm::FunctionType>(loweredType)) {
    TypeAST* ret = TypeAST::reconstruct(fnty->getReturnType());
    vector<TypeAST*> args;
    for (size_t i = 0; i < fnty->getNumParams(); ++i) {
       args.push_back(TypeAST::reconstruct(fnty->getParamType(i))); 
    }
    return FnTypeAST::get(ret, args, "fastcc");
  }

  if (const llvm::StructType* sty
         = llvm::dyn_cast<const llvm::StructType>(loweredType)) {
    seen[sty] = (TypeAST*) 1;
    vector<TypeAST*> args;
    for (size_t i = 0; i < sty->getNumElements(); ++i) {
       args.push_back(TypeAST::reconstruct(sty->getContainedType(i))); 
    }
    return TupleTypeAST::get(args);
  }
  
  if (const llvm::ArrayType* aty =
    llvm::dyn_cast<const llvm::ArrayType>(loweredType)) {
    // TODO add ArrayTypeAST...
    return new TypeAST(loweredType, SourceRange::getEmptyRange());
  }
  
  if (const llvm::OpaqueType* ty =
            llvm::dyn_cast<const llvm::OpaqueType>(loweredType)) {
    return new TypeAST(loweredType, SourceRange::getEmptyRange());
  }
  
  return TypeAST::get(loweredType);
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

map<RefTypeAST::RefTypeArgs, RefTypeAST*> RefTypeAST::refCache;

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
                          const vector<TypeAST*>& argTypes,
                          const std::string& callingConvName) {
  vector<const llvm::Type*> loweredArgTypes;
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

TypeAST* TupleTypeAST::getContainedType(size_t i) const {
  if (!indexValid(i)) return NULL;
  return parts[i];
}

map<TupleTypeAST::Args, TupleTypeAST*> TupleTypeAST::tupleTypeCache;

TupleTypeAST* TupleTypeAST::get(const vector<TypeAST*>& argTypes) {
  TupleTypeAST* tup = tupleTypeCache[argTypes];
  if (tup) return tup;

  vector<const llvm::Type*> loweredTypes;
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


const llvm::Type* ClosureTypeAST::getLLVMType() const {
  if (!repr) {
    clotype = genericClosureTypeFor(getFnType());
    const_cast<ClosureTypeAST*>(this)->repr = clotype->getLLVMType();
  }
  return repr;
}

/////////////////////////////////////////////////////////////////////

LiteralIntValueTypeAST* LiteralIntValueTypeAST::get(IntAST* intAST) {
  ASSERT(intAST) << "can't have an int with no int";
  return new LiteralIntValueTypeAST(intAST, intAST->sourceRange); 
}

LiteralIntValueTypeAST* LiteralIntValueTypeAST::get(uint64_t value,
                                            const SourceRange& sourceRange) {
  return new LiteralIntValueTypeAST(value, sourceRange); 
}

uint64_t LiteralIntValueTypeAST::getNumericalValue() const {
  if (intAST) {
    { TypecheckPass tp; intAST->accept(&tp);
      llvm::outs() << intAST->getOriginalText() << " ; "
                  << str(intAST->type) << "\n";
    }
    return getSaturating<uint64_t>(intAST->getConstantValue());
  } else {
    return value;
  }
}

/////////////////////////////////////////////////////////////////////

// static
SimdVectorTypeAST* SimdVectorTypeAST::get(LiteralIntValueTypeAST* size,
                                          TypeAST* type,
                                          const SourceRange& sourceRange) {
  llvm::VectorType* vecTy = llvm::VectorType::get(type->getLLVMType(),
                                                  size->getNumericalValue());
  return new SimdVectorTypeAST(vecTy, size, type, sourceRange);
}
