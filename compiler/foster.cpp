// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/DerivedTypes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
// We don't actually use the JIT, but we need this header for
// the TargetData member of the ExecutionEngine to be properly
// initialized to the host machine's native target.
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Linker.h"
#include "llvm/Support/StandardPasses.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Triple.h"
#include "llvm/System/Host.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegistry.h"
#include "llvm/Target/SubtargetFeature.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/IRReader.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/System/Signals.h"
#include "llvm/System/TimeValue.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"

#include "fosterLexer.h"
#include "fosterParser.h"

#include "FosterAST.h"
#include "ANTLRtoFosterAST.h"
#include "InputFile.h"

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

#define FOSTER_VERSION_STR "0.0.4"

struct ScopedTimer {
  ScopedTimer(llvm::Statistic& stat)
     : stat(stat), start(llvm::sys::TimeValue::now()) {}
  ~ScopedTimer() {
    llvm::sys::TimeValue end = llvm::sys::TimeValue::now();
    stat += (end - start).msec();
  }
private:
  llvm::Statistic& stat;
  llvm::sys::TimeValue start;
};

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

void createParser(ANTLRContext& ctx, const foster::InputFile& f) {
  assert(inbuf->getBufferSize() <= ((ANTLR3_UINT32)-1)
      && "Trying to parse files larger than 4GB makes me cry.");
  ctx.filename = f.getFilePath();
  ctx.input = antlr3NewAsciiStringInPlaceStream((pANTLR3_UINT8) f.getBuffer()->getBufferStart(),
                                                (ANTLR3_UINT32) f.getBuffer()->getBufferSize(),
                                                NULL);
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
  VariableAST* fnRef = new VariableAST(p->name, p->type);
  fnRef->lazilyInsertedPrototype = p;

  return fnRef;
}

VariableAST* proto(const Type* retTy, const std::string& fqName) {
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName));
}

VariableAST* proto(const Type* retTy, const std::string& fqName,
    TypeAST* ty1) {
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName,
       new VariableAST("p1", ty1)));
}

VariableAST* proto(const Type* retTy, const std::string& fqName,
    TypeAST* ty1, TypeAST* ty2) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1));
  inArgs.push_back(new VariableAST("p2", ty2));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs));
}

VariableAST* proto(const Type* retTy, const std::string& fqName,
    TypeAST* ty1, TypeAST* ty2, TypeAST* ty3) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1));
  inArgs.push_back(new VariableAST("p2", ty2));
  inArgs.push_back(new VariableAST("p3", ty3));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs));
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

std::set<std::string> globalNames;

void addToProperNamespace(VariableAST* var) {
  const string& fqName = var->name;
  globalNames.insert(fqName);

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
  enum intrinsic_kind { kTransform, kOverflow, kAtomicStub };
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

      // atomic.cmp.swap gets two int arguments instead of one
      { "atomic.cmp.swap", kAtomicStub, i8_to_i64 },

      // All the other atomic functions get just one int argument
      { "atomic.swap", kAtomicStub, i8_to_i64 },
      { "atomic.load.add", kAtomicStub, i8_to_i64 },
      { "atomic.load.sub", kAtomicStub, i8_to_i64 },
      { "atomic.load.and", kAtomicStub, i8_to_i64 },
      // LLVM's nand intrinsic is misleadingly named for backwards
      // compatibility with GCC 4.2;
      // it computes A & ~B instead of ~(A & B)
      //{ "atomic.load.nand", kAtomicStub, i8_to_i64 },
      { "atomic.load.or", kAtomicStub, i8_to_i64 },
      { "atomic.load.xor", kAtomicStub, i8_to_i64 },
      { "atomic.load.max", kAtomicStub, i8_to_i64 },
      { "atomic.load.min", kAtomicStub, i8_to_i64 },
      { "atomic.load.umax", kAtomicStub, i8_to_i64 },
      { "atomic.load.umin", kAtomicStub, i8_to_i64 },

      { NULL, kTransform, 0}
  };

  addToProperNamespace( proto(LLVMTypeFor("i64"), "llvm.readcyclecounter") );

  bit_intrinsic_spec* spec = spec_table;
  while (spec->intrinsicName) {
    unsigned size = 8;
    char ssize[16] = {0};
    while (size <= 64) {
      if (size & spec->sizeFlags) {
        sprintf(ssize, "i%d", size);
        TypeAST* ty = TypeAST::get(LLVMTypeFor(ssize));

        std::stringstream ss;
        ss << "llvm." << spec->intrinsicName << "." << ssize;

        if (spec->kind == kTransform) {
          // e.g for declaring i16 @llvm.bswap.i16(i16)
          addToProperNamespace( proto(ty->getLLVMType(), ss.str(), ty) );
        } else if (spec->kind == kOverflow) {
          std::vector<const Type*> params;
          params.push_back(ty->getLLVMType());
          params.push_back(LLVMTypeFor("i1"));
          const Type* retTy = llvm::StructType::get(getGlobalContext(), params, false);

          // e.g. for declaring {16,i1} @llvm.sadd.with.overflow.i16(i16, i16)
          addToProperNamespace( proto(retTy, ss.str(), ty, ty) );
        } else if (spec->kind == kAtomicStub) {
          // ss contains something like "llvm.atomic.cmp.swap.i32"
          ss << ".p0" << ssize; // now "llvm.atomic.cmp.swap.i32.p0i32"

          if (spec->intrinsicName == "atomic.cmp.swap") {
            // e.g. for declaring i32 @llvm.atomic.cmp.swap.i32.p0i32(i32*, i32, i32)
            addToProperNamespace( proto(ty->getLLVMType(), ss.str(),
                RefTypeAST::get(ty, false), ty, ty) );
          } else {
            // e.g. for declaring i32 @llvm.atomic.load.xor.i32.p0i32(i32*, i32)
            addToProperNamespace( proto(ty->getLLVMType(), ss.str(),
                RefTypeAST::get(ty, false), ty) );
          }
        }
      }
      size *= 2;
    }
    ++spec;
  }
}

static cl::opt<std::string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<bool>
optCompileSeparately("c",
  cl::desc("[foster] Compile separately, don't automatically link imported modules"));

static cl::opt<bool>
optDumpPreLinkedIR("dump-prelinked",
  cl::desc("[foster] Dump LLVM IR before linking with standard library"));

static cl::opt<bool>
optDumpPostLinkedIR("dump-postlinked",
  cl::desc("[foster] Dump LLVM IR after linking with standard library"));

static cl::opt<bool>
optDumpASTs("dump-asts",
  cl::desc("[foster] Dump intermediate ASTs (and ANLTR parse tree)"));

static cl::opt<bool>
optOptimizeZero("O0",
  cl::desc("[foster] Disable optimization passes after linking with standard library"));

static cl::list<const PassInfo*, bool, PassNameParser>
cmdLinePassList(cl::desc("Optimizations available:"));

void printVersionInfo() {
  std::cout << "Foster version: " << FOSTER_VERSION_STR;
  std::cout << ", compiled: " << __DATE__ << " at " << __TIME__ << std::endl;
  
  // TODO: could extract more detailed ANTLR version information
  // from the generated lexer/parser files...
  std::cout << "ANTLR version " << ANTLR_VERSION_STR << std::endl;
  
  cl::PrintVersionMessage(); 
}

#define DEBUG_TYPE "fosterc"
STATISTIC(statOptMs, "[foster] Time spent in LLVM IR optimization (ms)");
STATISTIC(statOverallRuntimeMs, "[foster] Overall compiler runtime (ms)");
STATISTIC(statParseTimeMs, "[foster] Time spent parsing input file (ms)");
STATISTIC(statFileIOMs, "[foster] Time spent doing non-parsing I/O (ms)");
STATISTIC(statLinkingMs, "[foster] Time spent linking LLVM modules (ms)");
STATISTIC(statIRtoAsmMs, "[foster] Time spent doing llc's job (IR->asm) (ms)");
STATISTIC(statPrettyPrintMs, "[foster] Time spent in pretty-printing (ms)");
STATISTIC(statTypeCheckingMs, "[foster] Time spent doing type checking (ms)");
STATISTIC(statCodegenMs, "[foster] Time spent doing Foster AST -> LLVM IR lowering (ms)");
STATISTIC(statClosureConversionMs, "[foster] Time spent performing closure conversion (ms)");

Module* readModuleFromPath(std::string path) {
  ScopedTimer timer(statFileIOMs);
  SMDiagnostic diag;
  return llvm::ParseIRFile(path, diag, llvm::getGlobalContext());

#if 0
  Module* m = NULL;
  std::string errMsg;
  // TODO test behavior with incorrect paths
  if (MemoryBuffer *memBuf = MemoryBuffer::getFile(path.c_str(), &errMsg)) {
    //if (m = getLazyBitcodeModule(memBuf, getGlobalContext(), &errMsg)) {
    
    // Currently, materalizing functions lazily fails with LLVM 2.6,
    // so this must be an ExistingModuleProvider
    if (m = ParseBitcodeFile(memBuf, getGlobalContext(), &errMsg)) {
      // Great!
    } else {
      std::cerr << "Error: could not parse module '" << path << "'" << std::endl;
      std::cerr << "\t" << errMsg << std::endl;
    }
    delete memBuf;
  }
  return m;
#endif
}

// Add module m's C-linkage functions in the global scopes,
// and also add prototypes to the linkee module.
void putModuleMembersInScope(Module* m, Module* linkee) {
  if (!m) return;

  for (Module::iterator it = m->begin(); it != m->end(); ++it) {
    const Function& f = *it;
    
    const std::string& name = f.getNameStr();
    bool isCxxLinkage = name[0] == '_' && name[1] == 'Z';

    bool hasDef = !f.isDeclaration();
    if (hasDef && !isCxxLinkage) {
      globalNames.insert(name);
      //std::cout << "Inserting ref to fn " << name << " in scopes" << std::endl;

      // Ensure that, when parsing, function calls to this name will find it
      const Type* ty = f.getType();
      // We get a pointer-to-whatever-function type, because f is a global
      // value (therefore ptr), but we want just the function type.
      if (const PointerType* pty = llvm::dyn_cast<PointerType>(ty)) {
        ty = pty->getElementType();
      }

      varScope.insert(name, new VariableAST(name, TypeAST::get(ty)));
      
      // Ensure that codegen for the given function finds the 'extern' declaration
      Value* decl = linkee->getOrInsertFunction(
          llvm::StringRef(name),
          llvm::dyn_cast<llvm::FunctionType>(ty),
          f.getAttributes());
      scope.insert(name, decl);
    }
  }
}


void dumpANTLRTreeNode(std::ostream& out, pTree tree, int depth) {
  out << string(depth, ' ');
  out << "text:"<< str(tree->getText(tree)) << " ";
  out << "line:"<< tree->getLine(tree) << " ";
  out << "charpos:"<< tree->getCharPositionInLine(tree) << " ";
  out << std::endl;
}

void dumpANTLRTree(std::ostream& out, pTree tree, int depth) {
  int nchildren = tree->getChildCount(tree);
  out << "nchildren:" << nchildren << std::endl;
  for (int i = 0; i < nchildren; ++i) {
    dumpANTLRTree(out, (pTree) tree->getChild(tree, i), depth + 1);
  }
  dumpANTLRTreeNode(out, tree, depth);
}

std::string dumpdir("fc-output/");
std::string dumpdirFile(const std::string& filename) {
  return dumpdir + filename;
}
void dumpModuleToFile(Module* mod, const std::string& filename) {
  ScopedTimer timer(statFileIOMs);
  std::string errInfo;
  llvm::raw_fd_ostream LLpreASM(filename.c_str(), errInfo);
  if (errInfo.empty()) {
    LLpreASM << *mod;
  } else {
    std::cerr << "Error dumping module to " << filename << std::endl;
    std::cerr << errInfo << std::endl;
    exit(1);
  }
}

void dumpModuleToBitcode(Module* mod, const std::string& filename) {
  ScopedTimer timer(statFileIOMs);
  std::string errInfo;
  sys::RemoveFileOnSignal(sys::Path(filename), &errInfo);

  raw_fd_ostream out(filename.c_str(), errInfo, raw_fd_ostream::F_Binary);
  if (!errInfo.empty()) {
    std::cerr << "Error when preparing to write bitcode to " << filename
        << "\n" << errInfo << std::endl;
    exit(1);
  }

  WriteBitcodeToFile(mod, out);
}

TargetData* getTargetDataForModule(Module* mod) {
  const std::string& layout = mod->getDataLayout();
  if (layout.empty()) return NULL;
  return new TargetData(layout);
}

void optimizeModuleAndRunPasses(Module* mod) {
  ScopedTimer timer(statOptMs);
  PassManager passes;
  FunctionPassManager fpasses(mod);

  TargetData* td = getTargetDataForModule(mod);
  if (td) {
    passes.add(td);
    fpasses.add(new TargetData(*td));
  } else {
    std::cout << "Warning: no target data for module!" << std::endl;
  }

  passes.add(llvm::createVerifierPass());

  if (!optOptimizeZero) {
    llvm::createStandardModulePasses(&passes, 2,
        /*OptimizeSize*/ false,
        /*UnitAtATime*/ true,
        /*UnrollLoops*/ true,
        /*SimplifyLibCalls*/ true,
        /*HaveExceptions*/ false,
        llvm::createFunctionInliningPass());
    llvm::createStandardLTOPasses(&passes,
        /*Internalize*/ true,
        /*RunInliner*/ true,
        /*VerifyEach*/ true);
  }

  // Add command line passes
  for (int i = 0; i < cmdLinePassList.size(); ++i) {
    const PassInfo* pi = cmdLinePassList[i];
    llvm::Pass* p = (pi->getNormalCtor()) ? pi->getNormalCtor()() : NULL;
    if (p) {
      passes.add(p);
    } else {
      std::cerr << "Error: unable to create pass " << pi->getPassName() << std::endl;
    }
  }

  if (!optOptimizeZero) {
    llvm::createStandardModulePasses(&passes, 3,
        /*OptimizeSize*/ false,
        /*UnitAtATime*/ true,
        /*UnrollLoops*/ true,
        /*SimplifyLibCalls*/ true,
        /*HaveExceptions*/ false,
        llvm::createFunctionInliningPass());

    passes.add(llvm::createVerifierPass());

    llvm::createStandardFunctionPasses(&fpasses, 2);
    llvm::createStandardFunctionPasses(&fpasses, 3);
  }

  fpasses.doInitialization();
  for (Module::iterator it = mod->begin(); it != mod->end(); ++it) {
    fpasses.run(*it);
  }
  fpasses.doFinalization();

  passes.run(*mod);
}

void compileToNativeAssembly(Module* mod, const std::string& filename) {
  ScopedTimer timer(statIRtoAsmMs);

  llvm::Triple triple(mod->getTargetTriple());
  if (triple.getTriple().empty()) {
    triple.setTriple(llvm::sys::getHostTriple());
  }

  const Target* target = NULL;
  std::string err;
  target = llvm::TargetRegistry::lookupTarget(triple.getTriple(), err);
  if (!target) {
    std::cerr << "Unable to pick a target for compiling to assembly!" << std::endl;
    exit(1);
  }

  TargetMachine* tm = target->createTargetMachine(triple.getTriple(), "");
  if (!tm) {
    std::cerr << "Error! Creation of target machine"
        " failed for triple " << triple.getTriple() << std::endl;
    exit(1);
  }

  tm->setAsmVerbosityDefault(true);

  // TODO replace TargetData from ee (in Codegen) with this TargetData
  FunctionPassManager passes(mod);
  if (const TargetData* td = tm->getTargetData()) {
    passes.add(new TargetData(*td));
  } else {
    passes.add(new TargetData(mod));
  }

  bool disableVerify = true;

  llvm::raw_fd_ostream raw_out(filename.c_str(), err, 0);
  if (!err.empty()) {
    std::cerr << "Error when opening file to print assembly to:\n\t"
        << err << std::endl;
    exit(1);
  }
  llvm::formatted_raw_ostream out(raw_out,
      llvm::formatted_raw_ostream::PRESERVE_STREAM);
  if (tm->addPassesToEmitFile(passes, out,
      TargetMachine::CGFT_AssemblyFile,
      CodeGenOpt::Aggressive,
      disableVerify)) {
    std::cerr << "Unable to emit assembly file! " << std::endl;
    exit(1);
  }

  passes.doInitialization();
  for (Module::iterator it = mod->begin(); it != mod->end(); ++it) {
    if (it->isDeclaration()) continue;
    passes.run(*it);
  }
  passes.doFinalization();
}

void validateInputFile(const std::string& pathstr) {
  llvm::sys::PathWithStatus path(pathstr);

  if (path.empty()) {
    std::cerr << "Error: need an input filename!" << std::endl;
    exit(1);
  }

  std::string err;
  const llvm::sys::FileStatus* status
         = path.getFileStatus(/*forceUpdate=*/ false, &err);
  if (!status) {
    if (err.empty()) {
      std::cerr << "Error occurred when reading input path '"
                << pathstr << "'" << std::endl;
    } else {
      std::cerr << err << std::endl;
    }
    exit(1);
  }

  if (status->isDir) {
    std::cerr << "Error: input must be a file, not a directory!" << std::endl;
    exit(1);
  }
}


int main(int argc, char** argv) {
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;

  ScopedTimer wholeProgramTimer(statOverallRuntimeMs);

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler\n");

  validateInputFile(optInputPath);

  { ScopedTimer timer(statFileIOMs);
    system(("mkdir -p " + dumpdir).c_str());

    std::cout << "Compiling separately? " << optCompileSeparately << std::endl;
    if (optDumpASTs) {
      std::cout << "Input file: " << optInputPath << std::endl;
      std::cout <<  "================" << std::endl;
      system(("cat " + optInputPath).c_str());
      std::cout <<  "================" << std::endl;
    }
  }
  
  fosterInitializeLLVM();
  module = new Module("foster", getGlobalContext());
  ee = EngineBuilder(module).create();
  initMaps();

  foster::InputFile infile(optInputPath);
  foster::gInputFile = &infile;

  ScopedTimer* timer = new ScopedTimer(statParseTimeMs); 
  ANTLRContext ctx;
  createParser(ctx, infile);
  fosterParser_program_return langAST = ctx.psr->program(ctx.psr);
  delete timer; // not block-scoped to allow proper binding of langAST

  if (optDumpASTs) { ScopedTimer timer(statFileIOMs);
    std::cout << "dumping parse trees" << endl;
    {
      std::ofstream out(dumpdirFile("stringtree.dump.txt").c_str());
      out << str(langAST.tree->toStringTree(langAST.tree)) << endl;
    }
    {
      std::ofstream out(dumpdirFile("parsetree.dump.txt").c_str());
      dumpANTLRTree(out, langAST.tree, 0);
    }
  }
  
  // TODO: I think the LLVM Type* of a module should be
  // a struct containing the elements of the underlying module?
  // This would be consistent with the dot (selection) operator
  // for accessing elements of the module.
 
  Module* m = readModuleFromPath("libfoster.bc");
  putModuleMembersInScope(m, module);
  
  createLLVMBitIntrinsics();

  std::cout << "converting" << endl;
  recursivelySetParentPointers(langAST.tree);
  langAST.tree->setParent(langAST.tree, NULL);
  ExprAST* exprAST = ExprAST_from(langAST.tree, false);

  { ScopedTimer timer(statFileIOMs);
  if (optDumpASTs) {
    std::string outfile = "ast.dump.1.txt";
    std::cout << "unparsing to " << outfile << endl;
    std::ofstream out(dumpdirFile(outfile).c_str());
    out << *exprAST << endl;
  }
  
  std::cout << "=========================" << std::endl;
  std::cout << "Adding parent links..." << std::endl;
  }

  { AddParentLinksPass aplPass; exprAST->accept(&aplPass); }
 
  { ScopedTimer timer(statFileIOMs);
  std::cout << "=========================" << std::endl;
  std::cout << "Type checking... " << std::endl;
  }

  { ScopedTimer timer(statTypeCheckingMs);
    TypecheckPass tyPass; exprAST->accept(&tyPass);
  }

  bool sema = exprAST->type != NULL;
  std::cout << "Semantic checking: " << sema << endl;
  if (!sema) { return 1; }
  
  if (optDumpASTs) { ScopedTimer timer(statFileIOMs);
    std::string outfile = "pp-precc.txt";
    std::cout << "=========================" << std::endl;
    std::cout << "Pretty printing to " << outfile << std::endl;
    std::ofstream out(dumpdirFile(outfile).c_str());
    ScopedTimer pptimer(statPrettyPrintMs);
    PrettyPrintPass ppPass(out); exprAST->accept(&ppPass); ppPass.flush();
  }

  { ScopedTimer timer(statFileIOMs);
    std::cout << "=========================" << std::endl;
    std::cout << "Performing closure conversion..." << std::endl;
  }

  { ScopedTimer timer(statClosureConversionMs);
    ClosureConversionPass p(globalNames); exprAST->accept(&p);
  }

  { ScopedTimer timer(statFileIOMs);
    std::string outfile = "pp-postcc.txt";
    std::cout << "=========================" << std::endl;
    std::cout << "Pretty printing to " << outfile << std::endl;
    std::ofstream out(dumpdirFile(outfile).c_str());
    ScopedTimer pptimer(statPrettyPrintMs);
    PrettyPrintPass ppPass(out); exprAST->accept(&ppPass); ppPass.flush();
  }

  std::cout << "=========================" << std::endl;

  {
    ScopedTimer timer(statCodegenMs);
    CodegenPass cgPass; exprAST->accept(&cgPass);
  }
  
  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module, dumpdirFile("out.prelink.ll").c_str());
  }

  if (!optCompileSeparately) {
    std::string errMsg;
    {
      ScopedTimer timer(statLinkingMs);
    if (Linker::LinkModules(module, m, &errMsg)) {
      std::cerr << "Error when linking modules together: " << errMsg << std::endl;
    }
    }

    if (optDumpPostLinkedIR) {
      dumpModuleToFile(module, "out.ll");
    }

    // Okay, this is a gross hack.
    // LLVM doesn't seem to want to do anything with the linked
    // module other than print it out to an IR file. In particular,
    // running optimizations, module verification, and printing to bitcode
    // all fail. As far as I can tell, calls to functions in the
    // standard library are rejected because it's a "different" module.
    //
    // The "solution" (until I figure out how to keep everything in memory)
    // is to print out the module to a file, then read it directly back,
    // yielding a new module, which we can then optimize and spit back out again.

    optimizeModuleAndRunPasses(module);
    compileToNativeAssembly(module, dumpdirFile("out.s"));
  } else { // -c, compile to bitcode instead of native assembly
    dumpModuleToBitcode(module, dumpdirFile("out.bc"));
  }
  // TODO invoke g++ .s -> exe
  return 0;
}


