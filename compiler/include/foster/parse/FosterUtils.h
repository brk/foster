// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_UTILS_H
#define FOSTER_UTILS_H

namespace llvm {
  class Type;
}

// This is the (prefix) struct type for a foster coro.
extern llvm::Type* foster_generic_coro_t;

class TypeAST;
class FnTypeAST;
class TupleTypeAST;

// Converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }.
// FnTypeASTs marked as closures use this to calculate their type.
TupleTypeAST* genericClosureTypeFor(const FnTypeAST* ty);

// Checks that ty == { i32 (i8*, ...)*, i8* }.
// Used when emitting type maps.
bool isGenericClosureType(const llvm::Type* ty);

#endif

