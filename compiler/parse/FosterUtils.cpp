// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"
#include "parse/ParsingContext.h"
#include "parse/CompilationContext.h"

#include "llvm/Module.h"
#include "llvm/Instructions.h"
#include "llvm/Metadata.h"

#include <sstream>

using llvm::Type;
using llvm::getGlobalContext;
using llvm::FunctionType;

const char* llvmValueTag(const llvm::Value* v) {
  using llvm::isa;
  if (!v) return "<NULL Value>";

  if (isa<llvm::AllocaInst>(v))         return "AllocaInst";
  if (isa<llvm::LoadInst>(v))           return "LoadInst";
  if (isa<llvm::CallInst>(v))           return "CallInst";
  if (isa<llvm::StoreInst>(v))          return "StoreInst";
  if (isa<llvm::BinaryOperator>(v))     return "BinaryOperator";

  if (isa<llvm::Constant>(v))     return "Constant";
  if (isa<llvm::Argument>(v))     return "Argument";
  if (isa<llvm::GlobalValue>(v))  return "GlobalValue";
  if (isa<llvm::CastInst>(v))     return "CastInst";

  if (isa<llvm::GetElementPtrInst>(v))  return "GetElementPtrInst";
  if (isa<llvm::ICmpInst>(v))           return "ICmpInst";
  if (isa<llvm::FCmpInst>(v))           return "FCmpInst";
  if (isa<llvm::SelectInst>(v))         return "SelectInst";
  if (isa<llvm::ExtractElementInst>(v)) return "ExtractElementInst";
  if (isa<llvm::ExtractValueInst>(v))   return "ExtractValueInst";
  if (isa<llvm::SelectInst>(v))         return "SelectInst";
  if (isa<llvm::SwitchInst>(v))         return "SwitchInst";
  if (isa<llvm::InsertElementInst>(v))  return "InsertElementInst";
  if (isa<llvm::InsertValueInst>(v))    return "InsertValueInst";
  if (isa<llvm::PHINode>(v))            return "PHINode";
  if (isa<llvm::ReturnInst>(v))         return "ReturnInst";
  if (isa<llvm::BranchInst>(v))         return "BranchInst";
  if (isa<llvm::IndirectBrInst>(v))     return "IndirectBrInst";
  if (isa<llvm::InvokeInst>(v))         return "InvokeInst";
  if (isa<llvm::UnwindInst>(v))         return "UnwindInst";
  if (isa<llvm::TruncInst>(v))          return "TruncInst";
  if (isa<llvm::BitCastInst>(v))        return "BitCastInst";

  return "Unknown Value";
}

void markAsNonAllocating(llvm::CallInst* callInst) {
  llvm::Value* tru = llvm::ConstantInt::getTrue(llvm::getGlobalContext());
  llvm::MDNode* mdnode = llvm::MDNode::get(llvm::getGlobalContext(), &tru, 1);
  callInst->setMetadata("willnotgc", mdnode);
}

llvm::ConstantInt* getConstantInt64For(int64_t val) {
  return llvm::ConstantInt::get(Type::getInt64Ty(getGlobalContext()), val);
}

llvm::ConstantInt* getConstantInt32For(int val) {
  return llvm::ConstantInt::get(Type::getInt32Ty(getGlobalContext()), val);
}

bool isPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && p->getContainedType(0) == t;
}

// returns true if p == t**
bool isPointerToPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && isPointerToType(p->getContainedType(0), t);
}

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

    mod->addTypeName(freshName(ss.str()), cty->getLLVMType());

    namedClosureTypes[cty] = true;
  }
}

// Converts t1 (t2, t3)   to  t1 (i8*, t2, t3)
FnTypeAST* genericClosureVersionOf(const FnTypeAST* fnty, bool skipFirstArg) {
  TypeAST* envType = RefTypeAST::get(TypeAST::i(8));

  std::vector<TypeAST*> fnParams;
  fnParams.push_back(envType);

  int firstArg = skipFirstArg ? 1 : 0;
  for (int i = firstArg; i < fnty->getNumParams(); ++i) {
    fnParams.push_back(fnty->getParamType(i));
  }

  return FnTypeAST::get(fnty->getReturnType(), fnParams, "fastcc");
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
    FnTypeAST* newFnTy = genericClosureVersionOf(fnty, skipFirstArg);
    std::vector<TypeAST*> cloTypes;
    cloTypes.push_back(RefTypeAST::get(newFnTy));
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
  }
  return NULL;
}

bool isVoid(const llvm::Type* ty) {
  return ty == ty->getVoidTy(llvm::getGlobalContext());
}

bool isVoid(TypeAST* ty) {
  NamedTypeAST* namedTy = dynamic_cast<NamedTypeAST*>(ty);
  return namedTy && namedTy->getName() == "void";
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

