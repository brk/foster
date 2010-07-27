// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "FosterUtils.h"
#include "parse/FosterAST.h" // TODO this is just for LLVMTypeFor(), should break this dependency!

#include "base/Diagnostics.h"

#include "llvm/Module.h"

#include <sstream>

using llvm::Type;
using llvm::FunctionType;

bool canAssignType(TypeAST* from, TypeAST* to) {
  // TODO refine this!
  return from == to;
}

// Converts T (X, Y) and T (X, Y)* to T (X, Y)
FnTypeAST* tryExtractCallableType(TypeAST* ty) {
  if (RefTypeAST* r = dynamic_cast<RefTypeAST*>(ty)) {
    // Avoid doing full recursion on pointer types; fn* is callable,
    // but fn** is not.
    ty = r->getElementType();
  }
  if (FnTypeAST* f = dynamic_cast<FnTypeAST*>(ty)) { return f; }
  std::cerr << "RETURNING NULL for extracting function type from " << str(ty) << std::endl;
  return NULL;
}

std::map<const Type*, bool> namedClosureTypes;

void addClosureTypeName(llvm::Module* mod, const llvm::StructType* sty) {
  if (!mod) return;
  if (namedClosureTypes[sty]) return;

  std::stringstream ss;
  ss << "ClosureTy";
  FnTypeAST* fty = tryExtractCallableType(TypeAST::get(sty->getContainedType(0)));
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
static TupleTypeAST* genericClosureTypeFor(TypeAST* ty, bool skipFirstArg) {
  std::cout << "59: " << str(ty) << std::endl;
#if 0
  if (ClosureTypeAST* cloty = dynamic_cast<ClosureTypeAST*>(ty)) {
    ty = cloty->getFnType();
  }
#endif

  if (FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(ty)) {
    TypeAST* envType = RefTypeAST::get(TypeAST::get(LLVMTypeFor("i8")));

    std::vector<TypeAST*> fnParams;
    fnParams.push_back(envType);

    int firstArg = skipFirstArg ? 1 : 0;
    for (int i = firstArg; i < fnty->getNumParams(); ++i) {
      fnParams.push_back(fnty->getParamType(i));
    }

    // We can mark closures with whatever calling convention we want,
    // since closures are internal by definition.
    FnTypeAST* newFnTy = FnTypeAST::get(fnty->getReturnType(), fnParams, "fastcc");
    std::vector<TypeAST*> cloTypes;
    cloTypes.push_back(RefTypeAST::get(newFnTy));
    cloTypes.push_back(envType);
    TupleTypeAST* cloTy = TupleTypeAST::get(cloTypes);
    //std::cout << "GENERIC CLOSURE TYPE for " << *fnty << " is " << *cloTy << std::endl;
    return cloTy;
  } else {
    foster::EDiag() << "unable to extract fn type from " << str(ty) << "\n";
    return NULL;
  }
}

// converts t1 (t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericClosureTypeFor(TypeAST* ty) {
  return genericClosureTypeFor(ty, false);
}

// converts t1 (envty*, t2, t3) to { t1 (i8*, t2, t3)*, i8* }
TupleTypeAST* genericVersionOfClosureType(TypeAST* ty) {
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

// converts { T (env*, Y, Z)*, env* }   to   T (Y, Z)
FnTypeAST* originalFunctionTypeForClosureStructType(TypeAST* ty) {
  if (TupleTypeAST* tty = dynamic_cast<TupleTypeAST*>(ty)) {
    if (FnTypeAST* ft = tryExtractCallableType(tty->getContainedType(0))) {
      // Create a new function type without the env ptr
      std::vector<TypeAST*> originalArgTypes;
      for (int i = 1; i < ft->getNumParams(); ++i) {
	originalArgTypes.push_back(ft->getParamType(i));
      }
      FnTypeAST* rv = FnTypeAST::get(ft->getReturnType(),
                                     originalArgTypes,
                                     "fastcc");
#if 0
      ft->dumpParams();
      std::cout << "originalFunc...() " << str(ty) << " => " << str(ft) 
	<< ";;; " << ft->getNumParams() << " ;; to " << str(rv) << std::endl;
#endif
      return rv;
    }
  } else if (ClosureTypeAST* cloty = dynamic_cast<ClosureTypeAST*>(ty)) {
    return cloty->getFnType();
  }
  return NULL;
}

#if 0
const llvm::Type* recursivelySubstituteGenericClosureTypes(
                                    const llvm::Type* ty,
                                    bool isInClosureType) {
  if (llvm::isa<llvm::IntegerType>(ty)) { return ty; }
  
  if (const FunctionType* fnty = llvm::dyn_cast<FunctionType>(ty)) {
    TupleTypeAST* sty = NULL;
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
      recursivelySubstituteGenericClosureTypes(pty->getElementType(),
                                               isInClosureType),
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
#endif

bool isVoid(const llvm::Type* ty) {
  return ty == ty->getVoidTy(llvm::getGlobalContext());
}
bool isVoid(const TypeAST* ty) {
  return isVoid(ty->getLLVMType());
}

bool voidCompatibleReturnTypes(const llvm::FunctionType* expected,
                               const llvm::FunctionType* actual) {
  return isVoid(expected->getReturnType())
      || expected->getReturnType() == actual->getReturnType();
}

bool isPointerToCompatibleFnTy(const llvm::Type* ty,
                               const llvm::FunctionType* fnty) {
 if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
   if (const llvm::FunctionType* pfnty = llvm::dyn_cast<llvm::FunctionType>(
                                                     pty->getElementType())) {
     // Compatible means all parameters have same types, and return values are
     // either same, or pfnty has void and fnty has non-void return type.
     if (!voidCompatibleReturnTypes(pfnty, fnty)) { return false; }

     if (pfnty->getNumParams() != fnty->getNumParams()) { return false; }
     for (size_t i = 0; i < fnty->getNumParams(); ++i) {
       if (pfnty->getParamType(i) != fnty->getParamType(i)) {
         return false;
       }
     }

     return true;
   }
 }
 return false;
}
