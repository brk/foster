// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CODEGEN_IMPL_H
#define FOSTER_PASSES_CODEGEN_IMPL_H

#include "llvm/Module.h"
#include "llvm/DerivedTypes.h"
#include "parse/FosterSymbolTable.h"

#include <string>
#include <map>
#include <set>

using llvm::Value;

// Declarations for Codegen-typemaps.cpp
enum ArrayOrNot {
  YesArray, NotArray
};

llvm::GlobalVariable*
emitTypeMap(const llvm::Type* ty, std::string name,
            ArrayOrNot arrayStatus,
            llvm::Module* mod,
            std::vector<int> skippedOffsets);

void registerType(const llvm::Type* ty,
                  std::string       desiredName,
                  llvm::Module*     mod,
                  ArrayOrNot);

llvm::GlobalVariable* getTypeMapForType(const llvm::Type*, llvm::Module*, ArrayOrNot);

bool mightContainHeapPointers(const llvm::Type* ty);

const inline llvm::PointerType* ptrTo(const llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
}

// From CodegenUtils.cpp
void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr);
Value* getUnitValue();
Value* allocateMPInt();
llvm::Value* codegenPrimitiveOperation(const std::string& op,
                                       llvm::IRBuilder<>& b,
                                       const std::vector<Value*>& args);
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

////////////////////////////////////////////////////////////////////

struct LLModule;
struct LLExpr;
struct LLVar;

struct CodegenPass {
  typedef foster::SymbolTable<llvm::Value> ValueTable;
  typedef ValueTable::LexicalScope         ValueScope;
  ValueTable valueSymTab;
  std::map<llvm::Function*, llvm::Instruction*> allocaPoints;
  std::set<llvm::Value*> needsImplicitLoad;

  llvm::Instruction* getCurrentAllocaPoint();

  llvm::Module* mod;
  //llvm::DIBuilder* dib;
  llvm::StringSet<> knownNonAllocatingFunctions;

  explicit CodegenPass(llvm::Module* mod);

  ~CodegenPass() {
    //delete dib;
  }

  void codegen(LLModule*);
  void codegen(LLExpr*);

  llvm::Function* lookupFunctionOrDie(const std::string& fullyQualifiedSymbol);

  void markAsNeedingImplicitLoads(llvm::Value* v);
  void addEntryBB(llvm::Function* f);

  Value* emit(LLExpr* e, TypeAST* t);
  Value* autoload(Value* v);

  // Returns ty**, the stack slot containing a ty*.
  llvm::AllocaInst* emitMalloc(const llvm::Type* ty);

  // Returns array_type[elt_ty]**, the stack slot containing an array_type[elt_ty]*.
  Value* emitArrayMalloc(const llvm::Type* elt_ty, llvm::Value* n);

  Value* allocateMPInt();

  llvm::AllocaInst* storeAndMarkPointerAsGCRootKnownCtor(llvm::Value*, ArrayOrNot);
  llvm::AllocaInst* storeAndMarkPointerAsGCRootUnknownCtor(llvm::Value*);

  Value* emitCoroCreateFn(const llvm::Type* retTy,
                          const llvm::Type* argTypes);
  Value* emitCoroInvokeFn(const llvm::Type* retTy,
                          const llvm::Type* argTypes);
  Value* emitCoroYieldFn( const llvm::Type* retTy,
                          const llvm::Type* argTypes);

};

#endif // header guard

