// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_UTILS_H
#define FOSTER_UTILS_H

namespace llvm {
  class Type;
  class Module;
}

// This is the (prefix) struct type for a foster coro.
extern const llvm::Type* foster_generic_coro_t;

class TypeAST;
class FnTypeAST;
class TupleTypeAST;

bool canAssignType(TypeAST* from, TypeAST* to);

void addClosureTypeName(llvm::Module* mod, TupleTypeAST* ty);

// Converts T (X, Y) and T (X, Y)* to T (X, Y)
FnTypeAST* tryExtractCallableType(TypeAST* ty);

// Converts t1 (t2, t3)   to  t1 (i8*, t2, t3)
FnTypeAST* genericClosureVersionOf(const FnTypeAST* fn);

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericClosureTypeFor(const TypeAST* ty);

// converts t1 (envptrty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericVersionOfClosureType(const TypeAST* ty);

bool isVoid(TypeAST* ty);

bool isValidClosureType(const llvm::Type* ty);

// Checks that ty == { i32 (i8*, ...)*, i8* }
bool isGenericClosureType(const llvm::Type* ty);

// converts { T (env*, Y, Z)*, env* }   to   T (Y, Z)
FnTypeAST* originalFunctionTypeForClosureStructType(TypeAST*);

#endif

