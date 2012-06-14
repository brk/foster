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
            int8_t        ctorId,
            llvm::Module* mod,
            std::vector<int> skippedOffsets);

void registerStructType(StructTypeAST* structty,
                        std::string    desiredName,
                        int8_t         ctorId,
                        llvm::Module*  mod);
llvm::GlobalVariable* getTypeMapForType(TypeAST*, int8_t ctorId,
                                        llvm::Module*, ArrayOrNot);

inline llvm::PointerType* ptrTo(llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
}
bool mayContainGCablePointers(llvm::Type* ty);
bool containsGCablePointers(TypeAST* typ, llvm::Type* ty);
llvm::Constant* slotSizeOf(llvm::Type* ty);

// From CodegenUtils.cpp
void emitFosterAssert(llvm::Module* mod, llvm::Value* cond, const char* cstr);
void emitFosterArrayBoundsCheck(llvm::Module* mod, llvm::Value* idx64,
                                                   llvm::Value* len64,
                                                   const std::string& srclines);
Value* getUnitValue();
Value* allocateMPInt();
Value* getElementFromComposite(Value* compositeValue, int, const std::string& msg);
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

void extendWithImplementationSpecificProcs(CodegenPass* _pass,
                                           std::vector<LLProc*>& procs);
////////////////////////////////////////////////////////////////////

inline bool operator<(const CtorId& a, const CtorId& b) {
  if (a.smallId < b.smallId) return true;
  if (a.ctorName < b.ctorName) return true;
  if (a.typeName < b.typeName) return true;
  return false;
}

struct ltLLOcc {
  bool operator()(LLOccurrence* a, LLOccurrence* b) {
    if (a->var->getName() < b->var->getName()) { return true; }
    if (a->offsets        < b->offsets       ) { return true; }
    if (a->ctors          < b->ctors         ) { return true; }
    return false;
  }
};

struct LLModule;
struct LLExpr;
struct LLVar;
struct BlockBindings;
struct DataTypeAST;
struct LazyCoroPrimInfo;

struct CodegenPass {
  bool useGC;
  bool useNSW;
  bool useNUW;
  bool trackAllocSites;

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
  std::map<std::string, DataTypeAST*>           isKnownDataType;
  std::map<llvm::Function*, llvm::Instruction*> allocaPoints;
  std::map<std::string, LLProc*>                procs;
  std::set<llvm::Value*> needsImplicitLoad;

  llvm::Instruction* getCurrentAllocaPoint();

  llvm::Module* mod;
  //llvm::DIBuilder* dib;
  llvm::StringSet<> knownNonAllocatingFunctions;

  std::map<std::string,     LLBlock*>     fosterBlocks;
  WorklistLIFO<std::string, LLBlock*>   worklistBlocks;
  std::map<LLOccurrence*, llvm::AllocaInst*, ltLLOcc>  occSlots;
  std::map<std::string, llvm::Value*> staticStrings;

  explicit CodegenPass(llvm::Module* mod, bool useGC, bool nsw, bool nuw,
                       bool trackAllocSites);

  ~CodegenPass() {
    //delete dib;
  }

  void codegen(LLModule*);
  void codegen(LLExpr*);
  llvm::Value* emitPrimitiveOperation(const std::string& op,
                                      llvm::IRBuilder<>& b,
                                      const std::vector<Value*>& args);

  llvm::Function* lookupFunctionOrDie(const std::string& fullyQualifiedSymbol);

  llvm::Value* markAsNeedingImplicitLoads(llvm::Value* v);
  void addEntryBB(llvm::Function* f);

  void scheduleBlockCodegen(LLBlock* b);
  LLBlock* lookupBlock(const std::string& s) {
      scheduleBlockCodegen(fosterBlocks[s]);
      return fosterBlocks[s];
  }

  Value* emit(LLExpr* e, TypeAST* t);
  Value* autoload(Value* v, const char* suffix = ".autoload");

  // Returns ty**, the stack slot containing a ty*.
  llvm::AllocaInst* emitMalloc(TypeAST* typ, int8_t ctorId,
                                      std::string srclines, bool init);

  // Returns array_type[elt_ty]**, the stack slot containing an array_type[elt_ty]*.
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

