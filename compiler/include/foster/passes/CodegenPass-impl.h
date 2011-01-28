// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_CODEGEN_IMPL_H
#define FOSTER_PASSES_CODEGEN_IMPL_H

#include "parse/ExprASTVisitor.h"

#include "passes/CodegenPass.h"

#include "llvm/Module.h"
#include "llvm/DerivedTypes.h"
#include "parse/FosterSymbolTable.h"

#include <string>

// Declarations for Codegen-typemaps.cpp
llvm::GlobalVariable*
emitTypeMap(const llvm::Type* ty, std::string name, bool skipOffsetZero = false);

void registerType(const Type* ty, std::string desiredName,
                  llvm::Module* mod,
                  bool isClosureEnvironment = false);

llvm::GlobalVariable* getTypeMapForType(const llvm::Type*, llvm::Module* mod);

bool mightContainHeapPointers(const llvm::Type* ty);

Value* getElementFromComposite(Value* compositeValue, Value* idxValue);

const inline llvm::PointerType* ptrTo(const llvm::Type* t) {
  return llvm::PointerType::getUnqual(t);
}

llvm::Value* storeAndMarkPointerAsGCRoot(llvm::Value* val,
                                         llvm::Module* mod);

////////////////////////////////////////////////////////////////////

struct CodegenPass : public ExprASTVisitor {
  #include "parse/ExprASTVisitor.decls.inc.h"

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

  void codegen(ExprAST*);

  llvm::Value* lookup(const std::string& fullyQualifiedSymbol);

  // Returns ty**, the stack slot containing a ty*.
  llvm::Value* emitMalloc(const llvm::Type* ty);

  llvm::Value* allocateMPInt();

  Value* emitCoroCreateFn(const llvm::Type* retTy,
                          const llvm::Type* argTypes);
  Value* emitCoroInvokeFn(const llvm::Type* retTy,
                          const llvm::Type* argTypes);
  Value* emitCoroYieldFn( const llvm::Type* retTy,
                          const llvm::Type* argTypes);

};

#endif // header guard

