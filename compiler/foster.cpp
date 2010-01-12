// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/DerivedTypes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/Interpreter.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/ModuleProvider.h"
#include "llvm/Linker.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/IRBuilder.h"

#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/System/Signals.h"

#include "fosterLexer.h"
#include "fosterParser.h"

#include "FosterAST.h"
#include "ANTLRtoFosterAST.h"
#include "TypecheckPass.h"
#include "CodegenPass.h"
#include "PrettyPrintPass.h"

#include <cassert>
#include <memory>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <map>
#include <vector>

using namespace llvm;

using std::string;
using std::endl;

struct ANTLRContext {
  string filename;
  pANTLR3_INPUT_STREAM input;
  pfosterLexer lxr;
  pANTLR3_COMMON_TOKEN_STREAM tstream;
  pfosterParser psr;

  ~ANTLRContext() {
    psr     ->free  (psr);      psr     = NULL;
    tstream ->free  (tstream);  tstream = NULL;
    lxr     ->free  (lxr);      lxr     = NULL;
    input   ->close (input);    input   = NULL;
  }
};

void createParser(ANTLRContext& ctx, string filename) {
  ctx.filename = filename;
  ctx.input = antlr3AsciiFileStreamNew( (pANTLR3_UINT8) filename.c_str() );
  if (ctx.input == NULL) {
    ANTLR3_FPRINTF(stderr, "Unable to open file '%s' due to malloc()"
                   "failure.\n", (char*) ctx.filename.c_str());
    exit(1);
  }

  ctx.lxr = fosterLexerNew(ctx.input);

  if (ctx.lxr == NULL) {
    ANTLR3_FPRINTF(stderr, "Unable to create lexer\n");
    exit(ANTLR3_ERR_NOMEM);
  }

  ctx.tstream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT,
                                                 TOKENSOURCE(ctx.lxr));

  if (ctx.tstream == NULL) {
    ANTLR3_FPRINTF(stderr, "Out of memory trying to allocate token stream.\n");
    exit(ANTLR3_ERR_NOMEM);
  }

  ctx.psr = fosterParserNew(ctx.tstream);
  if (ctx.psr == NULL) {
    ANTLR3_FPRINTF(stderr, "Out of memory trying to allocate parser.\n");
    exit(ANTLR3_ERR_NOMEM);
  }
}

// |param| is used to construct the prototype for the function,
// and a different VariableAST is inserted into the symbol tables
void addExternSingleParamFn(const char* name, VariableAST* param) {
  PrototypeAST* p = new PrototypeAST(name, param);
  
  TypecheckPass typ; p->accept(&typ);
  CodegenPass   cp;  p->accept(&cp);
  
  VariableAST* fnRef = new VariableAST(name, p->type);
  
  varScope.insert(name, fnRef);
  
  
  scope.insert(name, p->value);
}

void addLibFosterRuntimeExterns() {
  VariableAST* x_i32 = new VariableAST("xi32", LLVMTypeFor("i32"));
  addExternSingleParamFn("print_i32",   x_i32);
  addExternSingleParamFn("print_i32x",  x_i32);
  addExternSingleParamFn("print_i32b",  x_i32);
  addExternSingleParamFn("expect_i32",  x_i32);
  addExternSingleParamFn("expect_i32x", x_i32);
  addExternSingleParamFn("expect_i32b", x_i32);
  
  VariableAST* x_i1 = new VariableAST("xi1", LLVMTypeFor("i1"));
  addExternSingleParamFn("print_i1",  x_i1);
  addExternSingleParamFn("expect_i1", x_i1);
  
  // Don't pop scopes, so they will be available for the "real" program
}

ModuleProvider* readModuleFromPath(std::string path) {
  ModuleProvider* mp = NULL;
  std::string errMsg;
  
  // TODO test behavior with incorrect paths
  if (MemoryBuffer *memBuf = MemoryBuffer::getFile(path.c_str(), &errMsg)) {
    //if (mp = getBitcodeModuleProvider(memBuf, getGlobalContext(), &errMsg)) {
    
    // Currently, materalizing functions lazily fails with LLVM 2.6,
    // so this must be an ExistingModuleProvider
    if (Module* m = ParseBitcodeFile(memBuf, getGlobalContext(), &errMsg)) {
      mp = new ExistingModuleProvider(m);
    } else {
      std::cerr << "Error: could not parse module '" << path << "'" << std::endl;
      std::cerr << "\t" << errMsg << std::endl;
    }
    delete memBuf;
  }

  return mp;
}

void putModuleMembersInScope(ModuleProvider* mp) {
  Module* m = mp->getModule();
  if (!m) return;
  
  // Lazily-materialized modules (claim to) have no definition of
  // unmaterialized functions (fair enough, but still...)
  // TODO: bring up issues found with lazy materialization in #llvm
  
  // Materializing functions individually fails with LLVM 2.6 in
  // BitcodeReader.cpp:219
  
  // Materializing the whole module at once fails with LLVM 2.6 in
  // BitstreamReader.h:474
  for (Module::iterator it = m->begin(); it != m->end(); ++it) {
    const Function& f = *it;
    
    const std::string& name = f.getNameStr();
    bool isCxxLinkage = name[0] == '_' && name[1] == 'Z';
    if (!isCxxLinkage) {
      std::string errMsg;
      if (mp->materializeFunction(it, &errMsg)) {
        std::cout << "Error materializing fn " << name << ": " << errMsg << std::endl;
      }
    }
    bool hasDef = !f.isDeclaration();
    std::cout << "\tfn " << name << "; def? " << hasDef << std::endl;
   
    
    if (hasDef && !isCxxLinkage) {
      std::cout << "Inserting ref to fn " << name << " in scopes" << std::endl;
      // Ensure that, when parsing, function calls to this name will find it
      const Type* ty = f.getType();
      if (const PointerType* pty = llvm::dyn_cast<PointerType>(ty)) {
        ty = pty->getElementType();
      }
      varScope.insert(name, new VariableAST(name, ty));
      
      // Ensure that codegen for the given function finds it
      scope.insert(name, it);
    }
  }
}

int main(int argc, char** argv) {
  if (argc < 2 || argv[1] == NULL) {
    std::cout << "Error: need an input filename!" << std::endl;
    exit(1);
  } else {
    std::cout << "Input file: " << std::string(argv[1]) << std::endl;
    std::cout <<  "================" << std::endl;
    system(("cat " + std::string(argv[1])).c_str());
    std::cout <<  "================" << std::endl;
  }
  
  // TODO support a -c option for separate compilation and linking
  bool compileSeparately = true;
  
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;

  ANTLRContext ctx;
  createParser(ctx, argv[1]);

  fosterLLVMInitializeNativeTarget();
  module = new Module("foster", getGlobalContext());
  ExistingModuleProvider* moduleProvider = new ExistingModuleProvider(module);

  ee = EngineBuilder(moduleProvider).create();
  
  initMaps();

  std::cout << "parsing" << endl;
  fosterParser_program_return langAST = ctx.psr->program(ctx.psr);

  std::cout << "printing" << endl;
  std::cout << str(langAST.tree->toStringTree(langAST.tree)) << endl << endl;
  
  
  scope.pushScope("root");
  varScope.pushScope("root");
  
  // TODO: I think the LLVM Type* of a module should be
  // a struct containing the elements of the underlying module?
  // This would be consistent with the dot (selection) operator
  // for accessing elements of the module.
  
  ModuleProvider* mp = NULL;
  if (compileSeparately) {
    addLibFosterRuntimeExterns();
  } else {
    readModuleFromPath("libfoster.bc");
    putModuleMembersInScope(mp);
  }
  
  std::cout << "converting" << endl;
  ExprAST* exprAST = ExprAST_from(langAST.tree, 0, false);

  std::cout << "=========================" << std::endl;
  std::cout << "unparsing" << endl;
  std::cout << *exprAST << endl;
  
  std::cout << "=========================" << std::endl;
  
  
  TypecheckPass tyPass; exprAST->accept(&tyPass);
  bool sema = exprAST->type != NULL;
  std::cout << "Semantic checking: " << sema << endl; 
  
  if (!sema) return 1;
  
  std::cout << "=========================" << std::endl;
  std::cout << "Pretty printing: " << std::endl;
  
  { PrettyPrintPass ppPass(std::cout); exprAST->accept(&ppPass); ppPass.flush(); }
  std::cout << std::endl;
  
  std::cout << "=========================" << std::endl;
  
  { CodegenPass cgPass; exprAST->accept(&cgPass); }
  
  if (!compileSeparately) {
    std::ofstream LLpreASM("foster.prelink.ll");
    LLpreASM << *module;
  
    std::string errMsg;
    // TODO why does declare i32 @expect_i1(i1) work against
    //               define  i32 @expect_i1(i8 zeroext %x)
    // when linked with llvm-ld, but not when linked with Linker?
    // Ok, so it's basically because the linker optimized out the function call
    // entirely, but then why would it do so if the types didn't match?
    if (Linker::LinkModules(module, mp->getModule(), &errMsg)) {
      std::cerr << "Error when linking modules together: " << errMsg << std::endl;
    }
  }
  
  std::ofstream LLASM("foster.ll");
  LLASM << *module;
  
  return 0;
}


