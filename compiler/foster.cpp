// vim: set foldmethod=marker :

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

Value* genMain() {
  //DefAST CMainFunc = DefAST(false, "", "main", emptyFormals, "Int", CMainExprs);
  //return CMainFunc.Codegen();
  return NULL;
}

void evalExpr(llvm::ExecutionEngine* ee, ExprAST* expr) {

}

int main(int argc, char** argv) {

  if (argc < 2 || argv[1] == NULL) {
    std::cout << "Error: need an input filename!" << std::endl;
    exit(1);
  }

  ANTLRContext ctx;
  createParser(ctx, argv[1]);

  fosterLLVMInitializeNativeTarget();
  LLVMContext& Context = getGlobalContext();
  TheModule = new Module("foster", Context);
  llvm::ExistingModuleProvider* moduleProvider = new llvm::ExistingModuleProvider(TheModule);

  ee = llvm::EngineBuilder(moduleProvider).create();

  initMaps();

  std::cout << "parsing" << endl;
  fosterParser_program_return langAST = ctx.psr->program(ctx.psr);

  std::cout << "printing" << endl;
  std::cout << str(langAST.tree->toStringTree(langAST.tree)) << endl << endl;

  std::cout << "converting" << endl;
  ExprAST* exprAST = ExprAST_from(langAST.tree);

  std::cout << "unparsing" << endl;
  std::cout << *exprAST << endl;

  Value* v = exprAST->Codegen();

  std::ofstream LLASM("foster.ll");

  LLASM << *TheModule;
  //LLASM << v;
  /*
  Value* Main = genMainDotMain();
  if (Main) {
     LLASM << *Main;
  }
  */

  return 0;
}


