// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_LLVM_UTILS_H
#define FOSTER_LLVM_UTILS_H

#include "llvm/System/DataTypes.h"

namespace llvm {
  class Type;
  class Module;
  class FunctionType;
  class ConstantInt;
  class Value;
  class CallInst;
}

const char* llvmValueTag(const llvm::Value* v);
void markAsNonAllocating(llvm::CallInst* callInst);

// returns true if p == t*
bool isPointerToType(const llvm::Type* p, const llvm::Type* t);

// returns true if p == t**
bool isPointerToPointerToType(const llvm::Type* p, const llvm::Type* t);

// A compatible function type matches at all arguments, except that the return type
// for the first may be void, and the return type for the second need not be.
bool isPointerToCompatibleFnTy(const llvm::Type* first, const llvm::FunctionType* second);

bool voidCompatibleReturnTypes(const llvm::FunctionType* expected,
                               const llvm::FunctionType* actual);

bool isVoid(const llvm::Type* ty);

llvm::ConstantInt* getConstantInt64For(int64_t val);
llvm::ConstantInt* getConstantInt32For(int val);

#endif
