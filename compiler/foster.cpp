// vim: set foldmethod=marker :
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
#include "llvm/PassManager.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/IRBuilder.h"

#include "fosterLexer.h"
#include "fosterParser.h"

#include "FosterAST.h"
#include "ANTLRtoFosterAST.h"

#include <cassert>
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

void addExternSingleParamFn_i32(const char* name, VariableAST* param) {
  PrototypeAST* p = new PrototypeAST(name, param);
  scope.insert(name, p->Codegen());
  varScope.insert(name, new VariableAST(name, p->GetType()));
}

void addLibFosterRuntimeExterns() {
  scope.pushScope("externs");
  varScope.pushScope("externs");
  
  VariableAST* x_i32 = new VariableAST("x", llvm::IntegerType::get(getGlobalContext(), 32));
  addExternSingleParamFn_i32("print_i32",   x_i32);
  addExternSingleParamFn_i32("print_i32x",  x_i32);
  addExternSingleParamFn_i32("print_i32b",  x_i32);
  addExternSingleParamFn_i32("expect_i32",  x_i32);
  addExternSingleParamFn_i32("expect_i32x", x_i32);
  addExternSingleParamFn_i32("expect_i32b", x_i32);
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
  
  addLibFosterRuntimeExterns();
  
  std::cout << "converting" << endl;
  ExprAST* exprAST = ExprAST_from(langAST.tree, 0, false);

  std::cout << "unparsing" << endl;
  std::cout << *exprAST << endl;
  
  std::cout << "Semantic checking: " << exprAST->Sema() << endl; 
  
  std::cout << "=========================" << std::endl;
  
  Value* v = exprAST->Codegen();

  std::ofstream LLASM("foster.ll");

  LLASM << *module;
  //LLASM << v;
  /*
  Value* Main = genMainDotMain();
  if (Main) {
     LLASM << *Main;
  }
  */

  return 0;
}


