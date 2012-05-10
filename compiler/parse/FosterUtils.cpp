// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/LLVMUtils.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"
#include "parse/ParsingContext.h"

#include <sstream>

#include "llvm/Module.h"

using llvm::Type;
using llvm::FunctionType;

llvm::Type* foster_generic_coro_t;

bool isValidClosureType(const llvm::Type* ty) {
  if (const llvm::StructType* sty =
         llvm::dyn_cast_or_null<const llvm::StructType>(ty)) {
    if (sty->getNumElements() != 2) return false;

    const llvm::Type* maybeEnvTy = sty->getElementType(1);
    const llvm::Type* maybePtrFn = sty->getElementType(0);
    if (const llvm::PointerType* ptrMaybeFn
            = llvm::dyn_cast<llvm::PointerType>(maybePtrFn)) {
      if (const llvm::FunctionType* fnty
            = llvm::dyn_cast<llvm::FunctionType>(ptrMaybeFn->getElementType())) {
        if (fnty->getNumParams() == 0) return false;
        if (fnty->isVarArg()) return false;
        if (maybeEnvTy == fnty->getParamType(0)) {
          return true;
        }
      }
    }
  }
  return false;
}

// Checks that ty == { ___ (i8*, ...)*, i8* }
bool isGenericClosureType(const llvm::Type* ty) {
  using foster::builder;
  if (const llvm::StructType* sty= llvm::dyn_cast<const llvm::StructType>(ty)) {
    if (!isValidClosureType(sty)) return false;
    if (sty->getContainedType(1) != builder.getInt8PtrTy()) return false;
    if (!sty->getContainedType(0)->isPointerTy()) return false;

    const llvm::Type* fnty = sty->getContainedType(0)->getContainedType(0);
    if (!fnty->isFunctionTy()) return false;
    if (!fnty->getNumContainedTypes() >= 2) return false;
    if (fnty->getContainedType(1) != builder.getInt8PtrTy()) return false;
    return true;
  }
  return false;
}

