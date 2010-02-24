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

#include "llvm/Support/CommandLine.h"
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
#include "AddParentLinksPass.h"
#include "PrettyPrintPass.h"
#include "ClosureConversionPass.h"

#include "pystring/pystring.h"

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

#define FOSTER_VERSION_STR "0.0.1"

// TODO: this isn't scalable...
#include "antlr3defs.h"
const char* ANTLR_VERSION_STR = PACKAGE_VERSION;

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

VariableAST* checkAndGetLazyRefTo(PrototypeAST* p) {
  { TypecheckPass typ; p->accept(&typ); }
  VariableAST* fnRef = new VariableAST(p->Name, p->type);
  fnRef->lazilyInsertedPrototype = p;

  return fnRef;
}

VariableAST* proto(const Type* retTy, const std::string& fqName, const Type* ty1, const Type* ty2) {
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName,
       new VariableAST("p1", ty1), new VariableAST("p2", ty2)));
}

VariableAST* proto(const Type* retTy, const std::string& fqName, const Type* ty1) {
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName,
       new VariableAST("p1", ty1)));
}

ExprAST* lookupOrCreateNamespace(ExprAST* ns, const string& part) {
  ExprAST* nsPart = ns->lookup(part, "");
  if (!nsPart) {
    NameResolverAST* nr = dynamic_cast<NameResolverAST*>(ns);
    if (nr) {
      return nr->newNamespace(part);
    } else {
      std::cerr << "Error: lookupOrCreateNamespace failed because ns did not contain"
          " an entry for '" << part << "' and ns was not a NameResolverAST* !" << std::endl;
    }
  }

  return nsPart;
}

void addToProperNamespace(VariableAST* var) {
  const string& fqName = var->Name;
  std::vector<string> parts;
  pystring::split(fqName, parts, ".");

  ExprAST* ns = varScope.lookup(parts[0], "");
  if (!ns) {
    std::cerr << "Error: could not find root namespace for fqName " << fqName << std::endl;
    return;
  }

  // Note, we ignore the last component when creating namespaces.
  int nIntermediates = parts.size() - 1;
  for (int i = 1; i < nIntermediates; ++i) {
    ns = lookupOrCreateNamespace(ns, parts[i]);
  }

  // For the leaf name, insert variable ref rather than new namespace
  NameResolverAST* parentNS = dynamic_cast<NameResolverAST*>(ns);
  if (parentNS) {
    parentNS->insert(parts.back(), var);
  } else {
    std::cerr << "Error: final parent namespace for fqName '"
              << fqName << "' was not a NameResolverAST" << std::endl;
  }
}

void createLLVMBitIntrinsics() {
  // Make the module heirarchy available to code referencing llvm.blah.blah.
  // (The NameResolverAST name is mostly a convenience for examining the AST).
  varScope.insert("llvm", new NameResolverAST("llvm intrinsics"));

  const unsigned i16_to_i64 = ((1<<4)|(1<<5)|(1<<6));
  const unsigned i8_to_i64 = ((1<<3)|i16_to_i64);
  enum intrinsic_kind { kTransform, kOverflow };
  struct bit_intrinsic_spec {
    const char* intrinsicName; // e.g. "bswap" becomes "llvm.bswap.i16", "llvm.bswap.i32" etc
    const intrinsic_kind kind;
    const unsigned sizeFlags;
  };

  bit_intrinsic_spec spec_table[]  = {
      { "bswap", kTransform, i16_to_i64 },
      { "ctpop", kTransform, i8_to_i64 },
      { "ctlz",  kTransform, i8_to_i64 },
      { "cttz",  kTransform, i8_to_i64 },

      { "uadd.with.overflow", kOverflow, i16_to_i64 },
      { "sadd.with.overflow", kOverflow, i16_to_i64 },
      { "usub.with.overflow", kOverflow, i16_to_i64 },
      { "ssub.with.overflow", kOverflow, i16_to_i64 },
      { "umul.with.overflow", kOverflow, i16_to_i64 },
      { "smul.with.overflow", kOverflow, i16_to_i64 },

      { NULL, kTransform, 0}
  };

  bit_intrinsic_spec* spec = spec_table;
  while (spec->intrinsicName) {
    unsigned size = 8;
    char ssize[16] = {0};
    while (size <= 64) {
      if (size & spec->sizeFlags) {
        sprintf(ssize, "i%d", size);
        const Type* ty = LLVMTypeFor(ssize);

        std::stringstream ss;
        ss << "llvm." << spec->intrinsicName << "." << ssize;

        if (spec->kind == kTransform) {
          addToProperNamespace( proto(ty, ss.str(), ty) );
        } else if (spec->kind == kOverflow) {
          std::vector<const Type*> params;
          params.push_back(ty);
          params.push_back(LLVMTypeFor("i1"));
          const Type* retTy = llvm::StructType::get(getGlobalContext(), params, false);

          addToProperNamespace( proto(retTy, ss.str(), ty, ty) );
        }
      }
      size *= 2;
    }
    ++spec;
  }
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

static cl::opt<std::string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<bool>
optCompileSeparately("c",
  cl::desc("Compile separately, don't automatically link imported modules"));

void printVersionInfo() {
  std::cout << "Foster version: " << FOSTER_VERSION_STR;
  std::cout << ", compiled: " << __DATE__ << " at " << __TIME__ << std::endl;
  
  // TODO: could extract more detailed ANTLR version information
  // from the generated lexer/parser files...
  std::cout << "ANTLR version " << ANTLR_VERSION_STR << std::endl;
  
  cl::PrintVersionMessage(); 
}

int main(int argc, char** argv) {  
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler\n");
  
  if (optInputPath.empty()) {
    std::cerr << "Error: need an input filename!" << std::endl;
    exit(1);
  }
  
  {
    std::cout << "Compiling separately? " << optCompileSeparately << std::endl;
    std::cout << "Input file: " << optInputPath << std::endl;
    std::cout <<  "================" << std::endl;
    system(("cat " + optInputPath).c_str());
    std::cout <<  "================" << std::endl;
  }
  
  ANTLRContext ctx;
  createParser(ctx, optInputPath.c_str());

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
  mp = readModuleFromPath("libfoster.bc");
  putModuleMembersInScope(mp);
  
  createLLVMBitIntrinsics();

  std::cout << "converting" << endl;
  ExprAST* exprAST = ExprAST_from(langAST.tree, 0, false);

  std::cout << "=========================" << std::endl;
  std::cout << "unparsing" << endl;
  std::cout << *exprAST << endl;
  
  std::cout << "=========================" << std::endl;
  
  { AddParentLinksPass aplPass; exprAST->accept(&aplPass); }

  { TypecheckPass tyPass; exprAST->accept(&tyPass); }
  bool sema = exprAST->type != NULL;
  std::cout << "Semantic checking: " << sema << endl;
  if (!sema) return 1;
  
  {
    std::cout << "=========================" << std::endl;
    std::cout << "Pretty printing: " << std::endl;
  
    PrettyPrintPass ppPass(std::cout); exprAST->accept(&ppPass); ppPass.flush();
  }
  std::cout << std::endl;

  {
    std::cout << "=========================" << std::endl;
    std::cout << "Performing closure conversion..." << std::endl;

    ClosureConversionPass p; exprAST->accept(&p);
  }

  {
    std::cout << "=========================" << std::endl;
    std::cout << "Pretty printing: " << std::endl;

    PrettyPrintPass ppPass(std::cout); exprAST->accept(&ppPass); ppPass.flush();
  }

  std::cout << std::endl;
  std::cout << "=========================" << std::endl;

  { CodegenPass cgPass; exprAST->accept(&cgPass); }
  
  if (!optCompileSeparately) {
    std::ofstream LLpreASM("foster.prelink.ll");
    LLpreASM << *module;
  
    std::string errMsg;
    if (Linker::LinkModules(module, mp->getModule(), &errMsg)) {
      std::cerr << "Error when linking modules together: " << errMsg << std::endl;
    }
  }
  
  std::ofstream LLASM("foster.ll");
  LLASM << *module;
  
  return 0;
}


