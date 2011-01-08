// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/LLVMUtils.h"

#include "llvm/Instructions.h"
#include "llvm/Metadata.h"
#include "llvm/LLVMContext.h"

#ifdef LLVM_29
#include "llvm/Support/FileSystem.h"
#include "llvm/ADT/SmallString.h"
#endif

using llvm::Type;
using llvm::getGlobalContext;


void makePathAbsolute(llvm::sys::Path& path) {
  path.makeAbsolute();
#ifdef LLVM_29
  llvm::SmallString<128> pathstr(path.str());
  llvm::error_code err = llvm::sys::fs::make_absolute(pathstr);
  ASSERT(err == llvm::errc::success) << err.message();
  path.set(pathstr);
#endif
}

const char* llvmValueTag(const llvm::Value* v) {
  using llvm::isa;
  if (!v) return "<NULL Value>";

  if (isa<llvm::AllocaInst>(v))         return "AllocaInst";
  if (isa<llvm::LoadInst>(v))           return "LoadInst";
  if (isa<llvm::CallInst>(v))           return "CallInst";
  if (isa<llvm::StoreInst>(v))          return "StoreInst";
  if (isa<llvm::BinaryOperator>(v))     return "BinaryOperator";

  if (isa<llvm::Constant>(v))           return "Constant";
  if (isa<llvm::Argument>(v))           return "Argument";
  if (isa<llvm::GlobalValue>(v))        return "GlobalValue";
  if (isa<llvm::CastInst>(v))           return "CastInst";

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

llvm::ConstantInt* getConstantInt32For(int32_t val) {
  return llvm::ConstantInt::get(Type::getInt32Ty(getGlobalContext()), val);
}

llvm::ConstantInt* getConstantInt8For(int8_t val) {
  return llvm::ConstantInt::get(Type::getInt8Ty(getGlobalContext()), val);
}

bool isPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && p->getContainedType(0) == t;
}

// returns true if p == t**
bool isPointerToPointerToType(const llvm::Type* p, const llvm::Type* t) {
  return p->isPointerTy() && isPointerToType(p->getContainedType(0), t);
}

bool isVoid(const llvm::Type* ty) {
  return ty == ty->getVoidTy(llvm::getGlobalContext());
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

