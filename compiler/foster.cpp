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
#include "TypecheckPass.h"
#include "CodegenPass.h"

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

// |param| is used to construct the prototype for the function,
// and a different VariableAST is inserted into the symbol tables
void addExternSingleParamFn(const char* name, VariableAST* param) {
  PrototypeAST* p = new PrototypeAST(name, param);
  
  // These "passes" are intentionally run in the "wrong" order...
  TypecheckPass typ; p->accept(&typ);
  CodegenPass   cp;  p->accept(&cp);
  
  VariableAST* fnRef = new VariableAST(name, p->type);
  
  std::cout << "\t\t\tInserting into symbol table " << name << " : " << fnRef << "\tof type '";
  if (p->type) {
    std::cout << *(p->type);
  } else std::cout << "<null type>";
  std::cout << "'" << std::endl;
  
  varScope.insert(name, fnRef);
  scope.insert(name, p->value);
}

void addLibFosterRuntimeExterns() {
  scope.pushScope("externs");
  varScope.pushScope("externs");
  
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

  std::cout << "=========================" << std::endl;
  std::cout << "unparsing" << endl;
  std::cout << *exprAST << endl;
  
  std::cout << "=========================" << std::endl;
  
  TypecheckPass tyPass; exprAST->accept(&tyPass);
  bool sema = exprAST->type != NULL;
  std::cout << "Semantic checking: " << sema << endl; 
  
  if (!sema) return 1;
  
  std::cout << "=========================" << std::endl;
  
  CodegenPass cgPass; exprAST->accept(&cgPass);

  std::ofstream LLASM("foster.ll");

  LLASM << *module;

  return 0;
}


