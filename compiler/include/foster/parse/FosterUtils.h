// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_UTILS_H
#define FOSTER_UTILS_H

namespace llvm {
  class Type;
  class Module;
  class FunctionType;
  class ConstantInt;
}

class TypeAST;
class FnTypeAST;
class TupleTypeAST;

// returns true if p == t*
bool isPointerToType(const llvm::Type* p, const llvm::Type* t);

// returns true if p == t**
bool isPointerToPointerToType(const llvm::Type* p, const llvm::Type* t);

bool canAssignType(TypeAST* from, TypeAST* to);

void addClosureTypeName(llvm::Module* mod, TupleTypeAST* ty);

// Converts T (X, Y) and T (X, Y)* to T (X, Y)
FnTypeAST* tryExtractCallableType(TypeAST* ty);

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericClosureTypeFor(TypeAST* ty);

// converts t1 (envptrty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericVersionOfClosureType(TypeAST* ty);

// A compatible function type matches at all arguments, except that the return type
// for the first may be void, and the return type for the second need not be.
bool isPointerToCompatibleFnTy(const llvm::Type* first, const llvm::FunctionType* second);

bool voidCompatibleReturnTypes(const llvm::FunctionType* expected,
                               const llvm::FunctionType* actual);

bool isVoid(const llvm::Type* ty);
bool isVoid(TypeAST* ty);

bool isValidClosureType(const llvm::Type* ty);

// Checks that ty == { i32 (i8*, ...)*, i8* }
bool isGenericClosureType(const llvm::Type* ty);

// converts { T (env*, Y, Z)*, env* }   to   T (Y, Z)
FnTypeAST* originalFunctionTypeForClosureStructType(TypeAST*);

llvm::ConstantInt* getConstantInt64For(int64_t val);
llvm::ConstantInt* getConstantInt32For(int val);

#endif

