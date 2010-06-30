// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_UTILS_H
#define FOSTER_UTILS_H

#include "llvm/DerivedTypes.h"
#include "FosterAST.h"

// returns true if p == t*
inline bool isPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && p->getContainedType(0) == t;
}

// returns true if p == t**
inline bool isPointerToPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && isPointerToType(p->getContainedType(0), t);
}

bool canAssignType(TypeAST* from, TypeAST* to);

void addClosureTypeName(llvm::Module* mod, const llvm::StructType* ty);

// Converts T (X, Y) and T (X, Y)* to T (X, Y)
const llvm::FunctionType* tryExtractCallableType(const llvm::Type* ty);

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericClosureTypeFor(const llvm::FunctionType* fnty);

// converts t1 (envptrty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericVersionOfClosureType(const llvm::FunctionType* fnty);

// A compatible function type matches at all arguments, except that the return type
// for the first may be void, and the return type for the second need not be.
bool isPointerToCompatibleFnTy(const llvm::Type* first, const llvm::FunctionType* second);

bool voidCompatibleReturnTypes(const llvm::FunctionType* expected,
                               const llvm::FunctionType* actual);

bool isVoid(const llvm::Type* ty);

bool isValidClosureType(const llvm::StructType* sty);

// converts { T (env*, Y, Z)*, env* }   to   T (Y, Z)
const llvm::FunctionType* originalFunctionTypeForClosureStructType(const llvm::StructType* sty);

#endif

