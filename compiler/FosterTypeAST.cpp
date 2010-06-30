// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "FosterTypeAST.h"
#include "FosterAST.h"

bool hasEqualRepr(TypeAST* src, TypeAST* dst) {
  return src->getLLVMType() == dst->getLLVMType();
}

bool isAutoConvertible(const llvm::Type* fromTy,
                       const llvm::Type* toTy) {
  // no case for i1 needed because equality is taken care of
  bool to8  = toTy == LLVMTypeFor("i8");
  bool to16 = toTy == LLVMTypeFor("i16");
  bool to32 = toTy == LLVMTypeFor("i32");
  bool to64 = toTy == LLVMTypeFor("i64");

  if (fromTy == LLVMTypeFor("i1")) {
    return /**/ to8 /*|| to16 || to32 || to64*/;
  } else if (fromTy == LLVMTypeFor("i8")) {
    return /*to8 ||*/ to16 || to32 || to64;
  } else if (fromTy == LLVMTypeFor("i16")) {
    return /*to8 || to16 ||*/ to32 || to64;
  } else if (fromTy == LLVMTypeFor("i32")) {
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
        return RefTypeAST::get(new TypeAST(pointee));
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
    for (int i = 0; i < fnty->getNumParams(); ++i) {
       args.push_back(TypeAST::get(fnty->getParamType(i))); 
    }
    return FnTypeAST::get(ret, args);
  }

  if (const llvm::StructType* sty
         = llvm::dyn_cast<const llvm::StructType>(loweredType)) {
    seen[sty] = (TypeAST*) 1;
    std::vector<TypeAST*> args;
    for (int i = 0; i < sty->getNumElements(); ++i) {
       args.push_back(TypeAST::get(sty->getContainedType(i))); 
    }
    return TupleTypeAST::get(args);
  }

  TypeAST* tyast = thinWrappers[loweredType];
  if (tyast) { return tyast; }
  tyast = new TypeAST(loweredType); 
  thinWrappers[loweredType] = tyast;
  return tyast;
}

////////////////////////////////////////////////////////////////////

// virtual
bool TypeAST::canConvertTo(TypeAST* otherType) {
  std::cout << str(this) << "  canConvertTo?  " << str(otherType) << std::endl;
  return arePhysicallyCompatible(
	       this->getLLVMType(),
	       otherType->getLLVMType());
}

////////////////////////////////////////////////////////////////////

std::map<RefTypeAST::RefTypeArgs, RefTypeAST*> RefTypeAST::refCache;

RefTypeAST* RefTypeAST::get(TypeAST* baseType, bool nullable /* = false */) {
  assert(baseType);

  RefTypeArgs args = std::make_pair(baseType, nullable);
  RefTypeAST* ref = refCache[args];
  if (ref) return ref;
  ref = new RefTypeAST(baseType, nullable);
  refCache[args] = ref;
  return ref;
}

RefTypeAST* RefTypeAST::getNullableVersionOf(TypeAST* ptrType) {
  assert(ptrType && ptrType->getLLVMType()->isPointerTy());
  if (RefTypeAST* ref = dynamic_cast<RefTypeAST*>(ptrType)) {
    return RefTypeAST::get(ref->getElementType(), true);
  } else {
    std::cerr << "Error! getNullableVersionOf() given non-ptr"
              "arg: " << str(ptrType) << std::endl;
    return NULL;
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

std::map<FnTypeAST::FnTypeArgs, FnTypeAST*> FnTypeAST::fnTypeCache;

FnTypeAST* FnTypeAST::get(TypeAST* returnType,
                          const std::vector<TypeAST*>& argTypes) {
  // TODO this is one reason why TypeAST* uniquing should be
  // a valid but not required optimization, unlike for the
  // underlying llvm::Type*s
  FnTypeAST::FnTypeArgs args = std::make_pair(returnType, argTypes);
  FnTypeAST* fnty = fnTypeCache[args];
  if (fnty) return fnty;
  
  std::vector<const llvm::Type*> loweredArgTypes;
  for (int i = 0; i < argTypes.size(); ++i) {
    loweredArgTypes.push_back(argTypes[i]->getLLVMType());
  } 
  fnty = new FnTypeAST(
	    llvm::FunctionType::get(returnType->getLLVMType(),
                                    loweredArgTypes, /*isVarArg=*/ false),
                       returnType,
                       argTypes);
  fnTypeCache[args] = fnty;
  return fnty;
}

/////////////////////////////////////////////////////////////////////

std::map<TupleTypeAST::Args, TupleTypeAST*> TupleTypeAST::tupleTypeCache;

TupleTypeAST* TupleTypeAST::get(const std::vector<TypeAST*>& argTypes) {
  TupleTypeAST* tup = tupleTypeCache[argTypes];
  if (tup) return tup;

  std::vector<const llvm::Type*> loweredTypes;
  for (int i = 0; i < argTypes.size(); ++i) {
    loweredTypes.push_back(argTypes[i]->getLLVMType());
  }
  const llvm::StructType* sty = llvm::StructType::get(
            llvm::getGlobalContext(), loweredTypes, /*isPacked=*/false);
  tup = new TupleTypeAST(sty, argTypes);
  tupleTypeCache[argTypes] = tup;
  return tup;
}
