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
using llvm::getGlobalContext;
using llvm::FunctionType;

const llvm::Type* foster_generic_coro_t;

// Converts T (X, Y) and T (X, Y)* to T (X, Y)
FnTypeAST* tryExtractCallableType(TypeAST* ty) {
  if (RefTypeAST* r = dynamic_cast<RefTypeAST*>(ty)) {
    // Avoid doing full recursion on pointer types; fn* is callable,
    // but fn** is not.
    ty = r->getElementType();
  }
  if (FnTypeAST* f = dynamic_cast<FnTypeAST*>(ty)) { return f; }
  //std::cerr << "RETURNING NULL for extracting function type from " << str(ty) << std::endl;
  return NULL;
}

std::map<TupleTypeAST*, bool> namedClosureTypes;

void addClosureTypeName(llvm::Module* mod, TupleTypeAST* cty) {
  if (!mod) return;
  if (namedClosureTypes[cty]) return;

  std::stringstream ss;
  ss << "ClosureTy";
  FnTypeAST* fty = tryExtractCallableType(cty->getContainedType(0));
  if (fty != NULL) {
    // Skip generic closure argument
    for (int i = 1; i < fty->getNumParams(); ++i) {
      ss << "_" << *(fty->getParamType(i)->getLLVMType());
    }
    ss << "_to_" << *(fty->getReturnType()->getLLVMType());

    mod->addTypeName(foster::ParsingContext::freshName(ss.str()),
                     cty->getLLVMType());

    namedClosureTypes[cty] = true;
  }
}

// Converts t1 (t2, t3)   to  t1 (i8*, t2, t3)*
FnTypeAST* genericClosureVersionOf(const FnTypeAST* fnty, bool skipFirstArg) {
  TypeAST* envType = RefTypeAST::get(TypeAST::i(8));

  std::vector<TypeAST*> fnParams;
  fnParams.push_back(envType);

  int firstArg = skipFirstArg ? 1 : 0;
  for (int i = firstArg; i < fnty->getNumParams(); ++i) {
    fnParams.push_back(fnty->getParamType(i));
  }

  FnTypeAST* f = new FnTypeAST(fnty->getReturnType(), fnParams,
                               fnty->getAnnots());
  f->markAsProc();
  return f;
}

FnTypeAST* genericClosureVersionOf(const FnTypeAST* fnty) {
  return genericClosureVersionOf(fnty, /*skipFirstArg*/ false);
}

// converts      t1 (t2, t3)      to { t1 (i8*, t2, t3)*, i8* }
// or    t1 (envty* nest, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
static TupleTypeAST* genericClosureTypeFor(const TypeAST* ty, bool skipFirstArg) {
  if (const FnTypeAST* fnty = dynamic_cast<const FnTypeAST*>(ty)) {
    TypeAST* envType = RefTypeAST::get(TypeAST::i(8));

    // We can mark closures with whatever calling convention we want,
    // since closures are internal by definition.
    FnTypeAST* newProcTy = genericClosureVersionOf(fnty, skipFirstArg);
    std::vector<TypeAST*> cloTypes;
    cloTypes.push_back(newProcTy);
    cloTypes.push_back(envType);
    TupleTypeAST* cloTy = TupleTypeAST::get(cloTypes);
    return cloTy;
  } else {
    foster::EDiag() << "unable to extract fn type from " << str(const_cast<TypeAST*>(ty)) << "\n";
    return NULL;
  }
}

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericClosureTypeFor(const TypeAST* ty) {
  return genericClosureTypeFor(ty, false);
}

// converts t1 (envty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericVersionOfClosureType(const TypeAST* ty) {
  return genericClosureTypeFor(ty, true);
}

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

// Checks that ty == { i32 (i8*, ...)*, i8* }
bool isGenericClosureType(const llvm::Type* ty) {
  using foster::builder;
  if (const llvm::StructType* sty= llvm::dyn_cast<const llvm::StructType>(ty)) {
    if (!isValidClosureType(sty)) return false;
    if (sty->getContainedType(1) != builder.getInt8PtrTy()) return false;
    if (!sty->getContainedType(0)->isPointerTy()) return false;

    const llvm::Type* fnty = sty->getContainedType(0)->getContainedType(0);
    if (!fnty->isFunctionTy()) return false;
    if (!fnty->getNumContainedTypes() >= 2) return false;
    if (fnty->getContainedType(0) != builder.getInt32Ty()) return false;
    if (fnty->getContainedType(1) != builder.getInt8PtrTy()) return false;
    return true;
  }
  return false;
}

