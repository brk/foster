// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "FosterTypeAST.h"

std::map<const llvm::Type*, TypeAST*> TypeAST::thinWrappers;

TypeAST* TypeAST::get(const llvm::Type* loweredType) {
  if (!loweredType) return NULL;

  assert(!loweredType->isPointerTy() &&
      "pointer types should become RefTypeASTs,"
      " not base TypeASTs!");

  TypeAST* tyast = thinWrappers[loweredType];
  if (tyast) { return tyast; }
  tyast = new TypeAST(loweredType); 
  thinWrappers[loweredType] = tyast;
  return tyast;
}

////////////////////////////////////////////////////////////////////

typedef std::pair<const llvm::Type*, bool>  RefTypeArgs;
std::map<RefTypeArgs, RefTypeAST*> RefTypeAST::refCache;

RefTypeAST* RefTypeAST::get(const llvm::Type* baseType, bool nullable) {
  assert(baseType);

  const llvm::Type* ptrType = llvm::PointerType::getUnqual(baseType);
  RefTypeAST* ref = refCache[std::make_pair(ptrType, nullable)];
  if (ref) return ref;
  ref = new RefTypeAST(ptrType, nullable);
  return ref;
}

RefTypeAST* RefTypeAST::getNullableVersionOf(const llvm::Type* ptrType) {
  assert(ptrType && ptrType->isPointerTy());
  return RefTypeAST::get(ptrType->getContainedType(0), true);
}
