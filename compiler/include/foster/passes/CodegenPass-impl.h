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

extern unsigned kDefaultHeapAlignment;

llvm::GlobalVariable*
emitTypeMap(llvm::Type* ty, std::string name,
            ArrayOrNot arrayStatus,
            CtorRepr   ctorRepr,
            llvm::Module* mod,
            std::vector<int> skippedOffsets);

void registerStructType(StructTypeAST* structty,
                        std::string    desiredName,
                        CtorRepr       ctorRepr,
                        llvm::Module*  mod);
llvm::GlobalVariable* getTypeMapForType(TypeAST*, CtorRepr ctorRepr,
                                        llvm::Module*, ArrayOrNot);

inline llvm::PointerType* ptrTo(llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
}
bool mayContainGCablePointers(llvm::Type* ty);
bool containsGCablePointers(TypeAST* typ, llvm::Type* ty);
llvm::Constant* slotSizeOf(llvm::Type* ty);

// From CodegenUtils.cpp
Value* signExtend(Value* v, llvm::Type* dst);
void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr);
void emitFosterArrayBoundsCheck(llvm::Module* mod, llvm::Value* idx64,
                                                   llvm::Value* len64,
                                                   const std::string& srclines);
Value* getUnitValue();
Value* getElementFromComposite(Value* compositeValue, int, const std::string& msg);
Value* getPointerToIndex(Value* compositeValue,
                         Value* idxValue,
                         const std::string& name);
void markGCRoot(llvm::AllocaInst* root, CodegenPass* pass);
llvm::AllocaInst* getAllocaForRoot(llvm::Instruction* root);
llvm::AllocaInst* CreateEntryAlloca(llvm::Type* ty,
                                    const std::string& name);
llvm::AllocaInst* stackSlotWithValue(llvm::Value* val,
                                     const std::string& name);

void extendWithImplementationSpecificProcs(CodegenPass* _pass,
                                           std::vector<LLProc*>& procs);
llvm::Constant* getConstantArrayOfString(const std::string& s);

////////////////////////////////////////////////////////////////////

inline bool operator<(const CtorId& a, const CtorId& b) {
  if (a.ctorRepr.smallId < b.ctorRepr.smallId) return true;
  if (a.ctorName < b.ctorName) return true;
  if (a.typeName < b.typeName) return true;
  return false;
}

inline bool operator<(const CtorInfo& a, const CtorInfo& b) {
  return a.ctorId < b.ctorId;
}

struct LLModule;
struct LLExpr;
struct LLVar;
struct BlockBindings;
struct DataTypeAST;
struct LazyCoroPrimInfo;

struct CodegenPass {
  CodegenPassConfig config;

  typedef foster::SymbolTable<llvm::Value> ValueTable;
  typedef ValueTable::LexicalScope         ValueScope;
  ValueTable valueSymTab;

  ValueScope* newScope(const std::string&);
  void insertScopedValue(const std::string&, llvm::Value*);
  void popExistingScope(ValueScope*);

  typedef std::map<std::pair<
           std::pair<bool, llvm::Type*>,
                           llvm::Type*>, llvm::Function*>
          LazyCoroPrimInfoMap;

  LazyCoroPrimInfoMap                           lazyCoroPrimInfo;
  std::map<std::string, CtorTagRepresentation>  dataTypeTagReprs;
  std::map<llvm::Function*, llvm::Instruction*> allocaPoints;
  std::map<std::string, LLProc*>                procs;

  llvm::Instruction* getCurrentAllocaPoint(); // used for inserting GC roots.

  llvm::Module* mod;
  //llvm::DIBuilder* dib;

  std::map<std::string,     LLBlock*>     fosterBlocks;
  WorklistLIFO<std::string, LLBlock*>   worklistBlocks;
  std::map<std::string, llvm::Value*> staticStrings;

  std::string currentProcName;

  explicit CodegenPass(llvm::Module* mod, CodegenPassConfig config);

  ~CodegenPass() {
    //delete dib;
  }

  void codegen(LLModule*);
  void codegen(LLExpr*);
  llvm::Value* emitPrimitiveOperation(const std::string& op,
                                      llvm::IRBuilder<>& b,
                                      const std::vector<Value*>& args);

  llvm::Value* lookupFunctionOrDie(const std::string& fullyQualifiedSymbol);

  void addEntryBB(llvm::Function* f);

  void scheduleBlockCodegen(LLBlock* b);
  LLBlock* lookupBlock(const std::string& s) {
      ASSERT(fosterBlocks.count(s) != 0) << "missing basic block: " << s;
      scheduleBlockCodegen(fosterBlocks[s]);
      return fosterBlocks[s];
  }

  Value* emitMalloc(TypeAST* typ, CtorRepr ctorRepr,
                                      std::string srclines, bool init);

  Value* emitArrayMalloc(TypeAST* elt_type, llvm::Value* n, bool init);

  Value* emitFosterPrimArrayLength(Value* arr);
  Value* emitFosterStringOfCString(Value* cstr, Value* sz);

  Value* getGlobalString(const std::string&);

  Value* allocateMPInt();

  llvm::AllocaInst* storeAndMarkPointerAsGCRoot(llvm::Value*);

  Value* emitCoroCreateFn(TypeAST* retType, TypeAST* argTypes);
  Value* emitCoroInvokeFn(llvm::Type* retTy,
                          llvm::Type* argTypes);
  Value* emitCoroYieldFn( llvm::Type* retTy,
                          llvm::Type* argTypes);
  void emitLazyCoroPrimInfo(bool isYield, llvm::Function* fn,
                           llvm::Type* retTy,
                           llvm::Type* argTypes);
};

#endif // header guard

