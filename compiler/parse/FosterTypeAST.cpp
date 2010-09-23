// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"
#include "parse/CompilationContext.h"
#include "base/Diagnostics.h"
#include "base/Assert.h"

#include "parse/FosterUtils.h"
#include "passes/TypecheckPass.h"

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
        if (s == (TypeAST*) 1) {
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
                   " not be passed to NamedTypeAST::get()! Got: "
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
#if 0
  if (RefTypeAST* other = dynamic_cast<RefTypeAST*>(otherType)) {
    if (isNullable() && !other->isNullable()) {
      return false;
    }
  }
#endif
  return TypeAST::canConvertTo(otherType);
}

/////////////////////////////////////////////////////////////////////

FnTypeAST* FnTypeAST::get(TypeAST* returnType,
                          const vector<TypeAST*>& argTypes,
                          const std::string& callingConvName) {
  ASSERT(returnType) << "FnTypeAST::get() needs non-NULL return type";

  return new FnTypeAST(returnType,
                       argTypes,
                       callingConvName,
                       SourceRange::getEmptyRange());
}

const llvm::Type* FnTypeAST::getLLVMType() const {
  if (!repr) {
    vector<const llvm::Type*> loweredArgTypes;
    for (size_t i = 0; i < argTypes.size(); ++i) {
      loweredArgTypes.push_back(argTypes[i]->getLLVMType());
    }

    repr = llvm::FunctionType::get(returnType->getLLVMType(),
                                   loweredArgTypes,
                                   /*isVarArg=*/ false);
  }
  return repr;
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
    tup = new TupleTypeAST(argTypes, SourceRange::getEmptyRange());
    tupleTypeCache[argTypes] = tup;
  }
  return tup;
}

/////////////////////////////////////////////////////////////////////

FnTypeAST*& ClosureTypeAST::getFnType() {
  if (!fntype) {
    foster::typecheck(this->proto);
    if (FnTypeAST* fnty = tryExtractCallableType(proto->type)) {
      fntype = fnty;
    }
  }
  return fntype;
}


const llvm::Type* ClosureTypeAST::getLLVMType() const {
  if (!repr) {
    FnTypeAST* fnty = const_cast<ClosureTypeAST*>(this)->getFnType();
    if (!fnty) { return NULL; }
    //ASSERT(fnty) << "Can't get the type of this closure without a fn type";

    clotype = genericClosureTypeFor(fnty);
    ASSERT(clotype) << "Closure had fnty but no closure type: "
        << str(fnty->getLLVMType())
        << foster::show(getSourceRange());

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
    return getSaturating(getConstantInt(intAST));
  } else {
    return value;
  }
}

/////////////////////////////////////////////////////////////////////

/*
// static
SimdVectorTypeAST* SimdVectorTypeAST::get(LiteralIntValueTypeAST* size,
                                          TypeAST* type,
                                          const SourceRange& sourceRange) {
  llvm::VectorType* vecTy = llvm::VectorType::get(type->getLLVMType(),
                                                  size->getNumericalValue());
  return new SimdVectorTypeAST(vecTy, size, type, sourceRange);
}
*/
