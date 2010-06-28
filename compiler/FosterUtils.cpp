// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "FosterUtils.h"
#include "FosterAST.h" // TODO this is just for LLVMTypeFor(), should break this dependency!

#include "llvm/Module.h"

#include <sstream>

using llvm::Type;
using llvm::FunctionType;

bool canAssignType(const Type* from, const Type* to) {
  // TODO refine this!
  return from == to;
}

const FunctionType* tryExtractCallableType(const Type* ty) {
  if (const llvm::PointerType* ptrTy = llvm::dyn_cast_or_null<llvm::PointerType>(ty)) {
    // Avoid doing full recursion on pointer types; fn* is callable,
    // but fn** is not.
    ty = ptrTy->getContainedType(0);
  }

  return llvm::dyn_cast_or_null<const llvm::FunctionType>(ty);
}

std::map<const Type*, bool> namedClosureTypes;

void addClosureTypeName(llvm::Module* mod, const llvm::StructType* sty) {
  if (!mod) return;
  if (namedClosureTypes[sty]) return;

  std::stringstream ss;
  ss << "ClosureTy";
  const FunctionType* fty = tryExtractCallableType(sty->getContainedType(0));
  if (fty != NULL) {
    // Skip generic closure argument
    for (int i = 1; i < fty->getNumParams(); ++i) {
      ss << "_" << *(fty->getParamType(i));
    }
    ss << "_to_" << *(fty->getReturnType());

    mod->addTypeName(freshName(ss.str()), sty);

    namedClosureTypes[sty] = true;
  }
}

// converts      t1 (t2, t3) to { t1 (i8* nest, t2, t3)*, i8* }
// or    t1 (envty* nest, t2, t3) to { t1 (i8* nest, t2, t3)*, i8* }
static const llvm::StructType* genericClosureTypeFor(const FunctionType* fnty, bool skipFirstArg) {
  const Type* envType = llvm::PointerType::get(LLVMTypeFor("i8"), 0);

  std::vector<const Type*> fnParams;
  fnParams.push_back(envType);

  int firstArg = skipFirstArg ? 1 : 0;
  for (int i = firstArg; i < fnty->getNumParams(); ++i) {
    fnParams.push_back(fnty->getParamType(i));
  }

  const Type* fnTy = llvm::FunctionType::get(fnty->getReturnType(), fnParams, /*isVarArg=*/ false);
  std::vector<const Type*> cloTypes;
  cloTypes.push_back(llvm::PointerType::get(fnTy, 0));
  cloTypes.push_back(envType);
  const llvm::StructType* cloTy = llvm::StructType::get(getGlobalContext(), cloTypes, /*isPacked=*/ false);
  //std::cout << "GENERIC CLOSURE TYPE for " << *fnty << " is " << *cloTy << std::endl;
  return cloTy;
}

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericClosureTypeFor(const FunctionType* fnty) {
  return genericClosureTypeFor(fnty, false);
}

// converts t1 (envty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
const llvm::StructType* genericVersionOfClosureType(const FunctionType* fnty) {
  return genericClosureTypeFor(fnty, true);
}

bool isValidClosureType(const llvm::StructType* sty) {
  if (sty->getNumElements() != 2) return false;
  
  const llvm::Type* maybeEnvTy = sty->getElementType(1);
  const llvm::Type* maybePtrFn = sty->getElementType(0);
  if (const llvm::PointerType* ptrMaybeFn = llvm::dyn_cast<llvm::PointerType>(maybePtrFn)) {
    if (const llvm::FunctionType* fnty = llvm::dyn_cast<llvm::FunctionType>(ptrMaybeFn->getElementType())) {
      if (fnty->getNumParams() == 0) return false;
      if (fnty->isVarArg()) return false;
      if (maybeEnvTy == fnty->getParamType(0)) {
        return true;
      }
    }
  }
  return false;
}

// converts { T (env*, Y, Z)*, env* }   to   T (Y, Z)
const llvm::FunctionType* originalFunctionTypeForClosureStructType(const llvm::StructType* sty) {
  if (const llvm::FunctionType* ft = tryExtractCallableType(sty->getContainedType(0))) {
    std::vector<const llvm::Type*> originalArgTypes;
    for (int i = 1; i < ft->getNumParams(); ++i) {
      originalArgTypes.push_back(ft->getParamType(i));
    }
    return llvm::FunctionType::get(ft->getReturnType(), originalArgTypes, /*isVarArg=*/ false);
  }
  return NULL;
}

const llvm::Type* recursivelySubstituteGenericClosureTypes(
                                    const llvm::Type* ty,
                                    bool isInClosureType) {
  if (llvm::isa<llvm::IntegerType>(ty)) { return ty; }
  if (const FunctionType* fnty = llvm::dyn_cast<FunctionType>(ty)) {
    const llvm::StructType* sty = NULL;
    if (isInClosureType) {
      sty = genericVersionOfClosureType(fnty); 
      std::cout << "Converted closure fnty " << *fnty << "\n\t"
                    << "to closure type " << *sty << std::endl;
    } else {
      sty = genericClosureTypeFor(fnty); 
      std::cout << "Converted fnty " << *fnty << "\n\t"
                    << "to closure type " << *sty << std::endl;
    }
    return sty;
  }
  if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    return llvm::PointerType::get(
      recursivelySubstituteGenericClosureTypes(pty->getElementType(), isInClosureType),
      pty->getAddressSpace());
  }
  
  if (const llvm::StructType* sty = llvm::dyn_cast<llvm::StructType>(ty)) {
    std::vector<const llvm::Type*> argTypes;
    bool isClosureType = isValidClosureType(sty);
    for (int i = 0; i < sty->getNumElements(); ++i) {
      argTypes.push_back(recursivelySubstituteGenericClosureTypes(
                              sty->getElementType(i), isInClosureType));
    }
    return llvm::StructType::get(getGlobalContext(), argTypes, sty->isPacked());
  }
  
  // vectors and opqaue types fall through unmodified
  return ty;
  
  // TODO: unions
  // TODO: arrays
}

bool isVoid(const llvm::Type* ty) {
  return ty == ty->getVoidTy(getGlobalContext());
}

bool voidCompatibleReturnTypes(const llvm::FunctionType* expected,
                               const llvm::FunctionType* actual) {
  return isVoid(expected->getReturnType())
      || expected->getReturnType() == actual->getReturnType();
}

bool isPointerToCompatibleFnTy(const llvm::Type* ty, const llvm::FunctionType* fnty) {
 if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
   if (const llvm::FunctionType* pfnty = llvm::dyn_cast<llvm::FunctionType>(pty->getElementType())) {
     // Compatible means all parameters have same types, and return values are either
     // same, or pfnty has void and fnty has non-void return type.
     if (!voidCompatibleReturnTypes(pfnty, fnty)) { return false; }

     if (pfnty->getNumParams() != fnty->getNumParams()) { return false; }
     for (int i = 0; i < fnty->getNumParams(); ++i) {
       if (pfnty->getParamType(i) != fnty->getParamType(i)) {
         return false;
       }
     }

     return true;
   }
 }
 return false;
}
