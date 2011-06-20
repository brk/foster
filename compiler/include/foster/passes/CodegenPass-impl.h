// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CODEGEN_IMPL_H
#define FOSTER_PASSES_CODEGEN_IMPL_H

#include "llvm/Module.h"
#include "llvm/DerivedTypes.h"
#include "parse/FosterSymbolTable.h"

#include <string>

using llvm::Value;

// Declarations for Codegen-typemaps.cpp
enum ArrayOrNot {
  YesArray, NotArray
};

llvm::GlobalVariable*
emitTypeMap(const llvm::Type* ty, std::string name,
            ArrayOrNot arrayStatus,
            llvm::Module* mod,
            bool skipOffsetZero = false);

void registerType(const llvm::Type* ty,
                  std::string       desiredName,
                  llvm::Module*     mod,
                  ArrayOrNot,
                  bool isClosureEnvironment = false);

llvm::GlobalVariable* getTypeMapForType(const llvm::Type*, llvm::Module*, ArrayOrNot);

bool mightContainHeapPointers(const llvm::Type* ty);

const inline llvm::PointerType* ptrTo(const llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
}

// From CodegenUtils.cpp
void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr);
Value* getUnitValue();
Value* emitMalloc(const llvm::Type* ty);
Value* allocateMPInt();
Value* getElementFromComposite(Value* compositeValue, Value* idxValue,
                               const std::string& msg);
Value* getPointerToIndex(Value* compositeValue,
                         Value* idxValue,
                         const std::string& name);
void markGCRoot(llvm::Value* root,
                llvm::Constant* meta,
                llvm::Module* mod);
llvm::AllocaInst* getAllocaForRoot(llvm::Instruction* root);
llvm::AllocaInst* CreateEntryAlloca(const llvm::Type* ty,
                                    const std::string& name);
llvm::AllocaInst* stackSlotWithValue(llvm::Value* val,
                                     const std::string& name);
llvm::Value* storeAndMarkPointerAsGCRoot(llvm::Value*,
                                         ArrayOrNot,
                                         llvm::Module*);

////////////////////////////////////////////////////////////////////

struct LLModule;
struct LLExpr;

struct CodegenPass {
  typedef foster::SymbolTable<llvm::Value> ValueTable;
  typedef ValueTable::LexicalScope         ValueScope;
  ValueTable valueSymTab;

  llvm::Module* mod;
  //llvm::DIBuilder* dib;

  explicit CodegenPass(llvm::Module* mod) : mod(mod) {
    //dib = new DIBuilder(*mod);
  }

  ~CodegenPass() {
    //delete dib;
  }

  void codegen(LLModule*);
  void codegen(LLExpr*);

  llvm::Value* lookup(const std::string& fullyQualifiedSymbol);

  // Returns ty**, the stack slot containing a ty*.
  llvm::Value* emitMalloc(const llvm::Type* ty);

  // Returns array_type[elt_ty]**, the stack slot containing an array_type[elt_ty]*.
  llvm::Value* emitArrayMalloc(const llvm::Type* elt_ty,
                               llvm::Value* n);

  llvm::Value* allocateMPInt();

  Value* emitCoroCreateFn(const llvm::Type* retTy,
                          const llvm::Type* argTypes);
  Value* emitCoroInvokeFn(const llvm::Type* retTy,
                          const llvm::Type* argTypes);
  Value* emitCoroYieldFn( const llvm::Type* retTy,
                          const llvm::Type* argTypes);

};

#endif // header guard

