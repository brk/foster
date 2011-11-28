// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CODEGEN_IMPL_H
#define FOSTER_PASSES_CODEGEN_IMPL_H

#include "llvm/Module.h"
#include "llvm/DerivedTypes.h"
#include "base/Worklist.h"
#include "parse/FosterSymbolTable.h"

#include "passes/FosterLL.h"

#include <string>
#include <map>
#include <set>

using llvm::Value;

struct TupleTypeAST;

// Declarations for Codegen-typemaps.cpp
enum ArrayOrNot {
  YesArray, NotArray
};

llvm::GlobalVariable*
emitTypeMap(llvm::Type* ty, std::string name,
            ArrayOrNot arrayStatus,
            int8_t        ctorId,
            llvm::Module* mod,
            std::vector<int> skippedOffsets);

void registerTupleType(TupleTypeAST* tupletyp,
                       std::string   desiredName,
                       int8_t        ctorId,
                       llvm::Module* mod);
llvm::GlobalVariable* getTypeMapForType(llvm::Type*, int8_t ctorId,
                                        llvm::Module*, ArrayOrNot);

bool mightContainHeapPointers(llvm::Type* ty);

inline llvm::PointerType* ptrTo(llvm::Type* t) {
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
llvm::AllocaInst* CreateEntryAlloca(llvm::Type* ty,
                                    const std::string& name);
llvm::AllocaInst* stackSlotWithValue(llvm::Value* val,
                                     const std::string& name);

////////////////////////////////////////////////////////////////////

struct LLModule;
struct LLExpr;
struct LLVar;
struct BlockBindings;
struct DataTypeAST;

struct CodegenPass {
  typedef foster::SymbolTable<llvm::Value> ValueTable;
  typedef ValueTable::LexicalScope         ValueScope;
  ValueTable valueSymTab;

  ValueScope* newScope(const std::string&);
  void insertScopedValue(const std::string&, llvm::Value*);
  void popExistingScope(ValueScope*);

  std::map<std::string, DataTypeAST*> isKnownDataType;
  std::map<llvm::Function*, llvm::Instruction*> allocaPoints;
  std::set<llvm::Value*> needsImplicitLoad;

  llvm::Instruction* getCurrentAllocaPoint();

  llvm::Module* mod;
  //llvm::DIBuilder* dib;
  llvm::StringSet<> knownNonAllocatingFunctions;

  std::map<std::string,     LLBlock*>     fosterBlocks;
  WorklistLIFO<std::string, LLBlock*>   worklistBlocks;
  std::map<llvm::Value*, std::map<std::vector<int>, llvm::AllocaInst*> > occSlots;

  explicit CodegenPass(llvm::Module* mod);

  ~CodegenPass() {
    //delete dib;
  }

  void codegen(LLModule*);
  void codegen(LLExpr*);

  llvm::Function* lookupFunctionOrDie(const std::string& fullyQualifiedSymbol);

  void markAsNeedingImplicitLoads(llvm::Value* v);
  void addEntryBB(llvm::Function* f);

  void scheduleBlockCodegen(LLBlock* b);
  LLBlock* lookupBlock(const std::string& s) {
      scheduleBlockCodegen(fosterBlocks[s]);
      return fosterBlocks[s];
  }

  Value* emit(LLExpr* e, TypeAST* t);
  Value* autoload(Value* v);

  // Returns ty**, the stack slot containing a ty*.
  llvm::AllocaInst* emitMalloc(llvm::Type* ty, int8_t ctorId);

  // Returns array_type[elt_ty]**, the stack slot containing an array_type[elt_ty]*.
  Value* emitArrayMalloc(llvm::Type* elt_ty, llvm::Value* n);

  Value* allocateMPInt();

  llvm::AllocaInst* storeAndMarkPointerAsGCRoot(llvm::Value*);

  Value* emitCoroCreateFn(llvm::Type* retTy,
                          llvm::Type* argTypes);
  Value* emitCoroInvokeFn(llvm::Type* retTy,
                          llvm::Type* argTypes);
  Value* emitCoroYieldFn( llvm::Type* retTy,
                          llvm::Type* argTypes);

};

#endif // header guard

