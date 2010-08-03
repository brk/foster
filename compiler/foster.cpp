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
#include "llvm/LinkAllPasses.h"
#include "llvm/PassManager.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Config/config.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegistry.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Target/SubtargetFeature.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/StandardPasses.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/IRReader.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/System/Host.h"
#include "llvm/System/Signals.h"
#include "llvm/System/TimeValue.h"

// These macros are conflicted between llvm/Config/config.h and antlr3config.h
#undef PACKAGE_BUGREPORT
#undef PACKAGE_NAME
#undef PACKAGE_STRING
#undef PACKAGE_TARNAME
#undef PACKAGE_VERSION

#include "base/Assert.h"
#include "base/InputFile.h"
#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h"
#include "parse/CompilationContext.h"

#include "passes/BuildCFG.h"
#include "passes/TypecheckPass.h"
#include "passes/CodegenPass.h"
#include "passes/AddParentLinksPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ClosureConversionPass.h"
#include "passes/DumpToProtobuf.h"

#include "pystring/pystring.h"

#include <cassert>
#include <memory>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>

using namespace llvm;

using foster::LLVMTypeFor;
using foster::SourceRange;
using foster::EDiag;

namespace foster {
  struct ScopeInfo;
  void linkFosterGC(); // defined in llmv/plugins/FosterGC.cpp
}

using std::string;

#define FOSTER_VERSION_STR "0.0.4"
extern const char* ANTLR_VERSION_STR;

class TimingsRepository {
  std::map<string, uint64_t> totals;
  std::map<string, uint64_t> locals;
  std::map<string, string> descriptions;

public:
  void describe(string path, string desc) {
    descriptions[path] += desc;
  }

  void incr(const char* dottedpath, uint64_t n) {
    std::vector<string> parts;
    pystring::split(dottedpath, parts, ".");

    locals[dottedpath] += n;

    string prefix;
    for (size_t i = 0; i < parts.size(); ++i) {
      if (i > 0) prefix += ".";
      prefix += parts[i];
      totals[prefix] += n;
    }
  }

  void print() {
    typedef std::map<string, uint64_t>::iterator Iter;
    size_t maxTotalLength = 0;
    for (Iter it = totals.begin(); it != totals.end(); ++it) {
      const string& s = (*it).first;
      maxTotalLength = (std::max)(maxTotalLength, s.size());
    }
    string pathFormatString;
    llvm::raw_string_ostream pfs(pathFormatString);
    pfs << "%-" << (maxTotalLength) << "s";
    pfs.flush();

    llvm::outs() << llvm::format(pathFormatString.c_str(), (const char*) "Category name")
        << "    Total" << "  " << "Local" << "\n";

    for (Iter it = totals.begin(); it != totals.end(); ++it) {
      const string& s = (*it).first;
      llvm::outs() << llvm::format(pathFormatString.c_str(), s.c_str())
                  << "  " << llvm::format("%5u", (unsigned) totals[s])
                  << "  "  << llvm::format("%5u", (unsigned) locals[s]);
      const string& d = descriptions[s];
      if (!d.empty()) {
        llvm::outs() << " -- " << d;
      }
      llvm::outs() << "\n";
    }
  }
};

TimingsRepository gTimings;

struct ScopedTimer {
  ScopedTimer(const char* stat)
     : stat(stat), start(llvm::sys::TimeValue::now()) {}
  ~ScopedTimer() {
    llvm::sys::TimeValue end = llvm::sys::TimeValue::now();
    gTimings.incr(stat, (end - start).msec());
  }
private:
  const char* stat;
  llvm::sys::TimeValue start;
};


VariableAST* checkAndGetLazyRefTo(PrototypeAST* p) {
  { TypecheckPass typ; p->accept(&typ); }
  VariableAST* fnRef = new VariableAST(p->name, p->type,
                              SourceRange::getEmptyRange());
  fnRef->lazilyInsertedPrototype = p;

  return fnRef;
}

VariableAST* proto(TypeAST* retTy, const string& fqName) {
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName,
                                    SourceRange::getEmptyRange()));
}

VariableAST* proto(TypeAST* retTy, const string& fqName,
    TypeAST* ty1) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1, SourceRange::getEmptyRange()));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs,
                                    SourceRange::getEmptyRange()));
}

VariableAST* proto(TypeAST* retTy, const string& fqName,
    TypeAST* ty1, TypeAST* ty2) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1, SourceRange::getEmptyRange()));
  inArgs.push_back(new VariableAST("p2", ty2, SourceRange::getEmptyRange()));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs,
                                    SourceRange::getEmptyRange()));
}

VariableAST* proto(TypeAST* retTy, const string& fqName,
    TypeAST* ty1, TypeAST* ty2, TypeAST* ty3) {
  std::vector<VariableAST*> inArgs;
  inArgs.push_back(new VariableAST("p1", ty1, SourceRange::getEmptyRange()));
  inArgs.push_back(new VariableAST("p2", ty2, SourceRange::getEmptyRange()));
  inArgs.push_back(new VariableAST("p3", ty3, SourceRange::getEmptyRange()));
  return checkAndGetLazyRefTo(new PrototypeAST(retTy, fqName, inArgs,
                                    SourceRange::getEmptyRange()));
}

ExprAST* lookupOrCreateNamespace(ExprAST* ns, const string& part) {
  ExprAST* nsPart = ns->lookup(part, "");
  if (nsPart) {
    return nsPart;
  }

  if (NamespaceAST* nr = dynamic_cast<NamespaceAST*>(ns)) {
    return nr->newNamespace(part);
  } else {
    EDiag() << "Error: lookupOrCreateNamespace failed because "
            << " ns did not contain an entry for '" << part << "'"
            << " and ns was not a NamespaceAST*";
  }
  return NULL;
}

std::set<string> globalNames;

void addToProperNamespace(VariableAST* var) {
  const string& fqName = var->name;
  globalNames.insert(fqName);

  std::vector<string> parts;
  pystring::split(fqName, parts, ".");

  ExprAST* ns = gScopeLookupAST(parts[0]);
  if (!ns) {
    llvm::errs() << "Error: could not find root namespace for fqName "
              << fqName << "\n";
    return;
  }

  // Note, we ignore the last component when creating namespaces.
  int nIntermediates = parts.size() - 1;
  for (int i = 1; i < nIntermediates; ++i) {
    ns = lookupOrCreateNamespace(ns, parts[i]);
  }

  // For the leaf name, insert variable ref rather than new namespace
  if (NamespaceAST* parentNS = dynamic_cast<NamespaceAST*>(ns)) {
    parentNS->insert(parts.back(), var);
  } else {
    llvm::errs() << "Error: final parent namespace for fqName '"
              << fqName << "' was not a NamespaceAST" << "\n";
  }
}

void createLLVMBitIntrinsics() {
  // Make the module heirarchy available to code referencing llvm.blah.blah.
  // (The NamespaceAST name is mostly a convenience for examining the AST).
  gScope.insert("llvm", new foster::SymbolInfo(
                           new NamespaceAST("llvm intrinsics",
                                            gScope.getRootScope(),
                                       foster::SourceRange::getEmptyRange())));

  const unsigned i16_to_i64 = ((1<<4)|(1<<5)|(1<<6));
  const unsigned i8_to_i64 = ((1<<3)|i16_to_i64);
  enum intrinsic_kind { kTransform, kOverflow, kAtomicStub };
  struct bit_intrinsic_spec {
    // e.g. "bswap" becomes "llvm.bswap.i16", "llvm.bswap.i32" etc
    const char* intrinsicName;
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
      { NULL, kTransform, 0}
  };

  addToProperNamespace( proto(TypeAST::i(64), "llvm.readcyclecounter") );

  bit_intrinsic_spec* spec = spec_table;
  while (spec->intrinsicName) {
    unsigned size = 8;
    while (size <= 64) {
      if (size & spec->sizeFlags) {
        TypeAST* ty = TypeAST::i(size);

        std::stringstream ss;
        ss << "llvm." << spec->intrinsicName << ".i" << size;

        if (spec->kind == kTransform) {
          // e.g for declaring i16 @llvm.bswap.i16(i16)
          addToProperNamespace( proto(ty, ss.str(), ty) );
        } else if (spec->kind == kOverflow) {
          std::vector<TypeAST*> params;
          params.push_back(ty);
          params.push_back(TypeAST::i(1));
          TypeAST* retTy = TupleTypeAST::get(params);

          // e.g. for declaring {16,i1} @llvm.sadd.with.overflow.i16(i16, i16)
          addToProperNamespace( proto(retTy, ss.str(), ty, ty) );
        } else if (spec->kind == kAtomicStub) {
          // ss contains something like "llvm.atomic.cmp.swap.i32"
          ss << ".p0i" << size; // now "llvm.atomic.cmp.swap.i32.p0i32"

          if (spec->intrinsicName == string("atomic.cmp.swap")) {
            // e.g. for declaring i32 @llvm.atomic.cmp.swap.i32.p0i32(i32*, i32, i32)
            addToProperNamespace( proto(ty, ss.str(),
                RefTypeAST::get(ty, false), ty, ty) );
          } else {
            // e.g. for declaring i32 @llvm.atomic.load.xor.i32.p0i32(i32*, i32)
            addToProperNamespace( proto(ty, ss.str(),
                RefTypeAST::get(ty, false), ty) );
          }
        }
      }
      size *= 2;
    }
    ++spec;
  }
}

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<bool>
optCompileSeparately("c",
  cl::desc("[foster] Compile separately, don't automatically link imported modules"));

#ifdef FOSTERC_DEBUG_INFO_NOT_YET_GENERATED
static cl::opt<bool>
optEmitDebugInfo("g",
  cl::desc("[foster] Emit debug information in generated code"));
#endif

static cl::opt<bool>
optDumpPreLinkedIR("dump-prelinked",
  cl::desc("[foster] Dump LLVM IR before linking with standard library"));

static cl::opt<bool>
optDumpPostLinkedIR("dump-postlinked",
  cl::desc("[foster] Dump LLVM IR after linking with standard library"));

static cl::opt<bool>
optDumpPostOptIR("dump-postopt",
  cl::desc("[foster] Dump LLVM IR after linking and optimization passes"));

static cl::opt<bool>
optDumpASTs("dump-asts",
  cl::desc("[foster] Dump intermediate ASTs (and ANLTR parse tree)"));

#ifdef LLVM_GE_2_8
static cl::opt<bool>
optDumpStats("dump-stats",
  cl::desc("[foster] Dump timing and other statistics from compilation"));
#endif

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("[foster] Print timing measurements of compiler passes"));

static cl::opt<bool>
optOptimizeZero("O0",
  cl::desc("[foster] Disable optimization passes after linking with standard library"));

static cl::list<const PassInfo*, bool, PassNameParser>
cmdLinePassList(cl::desc("Optimizations available:"));

void printVersionInfo() {
  llvm::outs() << "Foster version: " << FOSTER_VERSION_STR;
  llvm::outs() << ", compiled: " << __DATE__ << " at " << __TIME__ << "\n";
  llvm::outs() << "ANTLR version " << ANTLR_VERSION_STR << "\n";
  cl::PrintVersionMessage(); 
}

void setTimingDescriptions() {
  gTimings.describe("total", "Overall compiler runtime (ms)");

  gTimings.describe("io.parse", "Time spent parsing input file (ms)");
  gTimings.describe("io.file",  "Time spent doing non-parsing I/O (ms)");
  gTimings.describe("io.dot",   "Time spent writing DOT graphs (ms)");
  gTimings.describe("io.prettyprint", "Time spent in pretty-printing (ms)");

  gTimings.describe("llvm.opt",  "Time spent in LLVM IR optimization (ms)");
  gTimings.describe("llvm.link", "Time spent linking LLVM modules (ms)");
  gTimings.describe("llvm.llc",  "Time spent doing llc's job (IR->asm) (ms)");

  gTimings.describe("protobuf", "Time spent snogging protocol buffers (ms)");

  gTimings.describe("foster.typecheck", "Time spent doing type checking (ms)");
  gTimings.describe("foster.codegen",   "Time spent doing Foster AST -> LLVM IR lowering (ms)");
  gTimings.describe("foster.closureconv", "Time spent performing closure conversion (ms)");
}

void ensureDirectoryExists(const string& pathstr) {
  llvm::sys::Path p(pathstr);
  if (!p.isDirectory()) {
    p.createDirectoryOnDisk(true, NULL);
  }
}

Module* readModuleFromPath(string path) {
  ScopedTimer timer("io.file.readmodule");
  SMDiagnostic diag;
  return llvm::ParseIRFile(path, diag, llvm::getGlobalContext());
}

// Add module m's C-linkage functions in the global scopes,
// and also add prototypes to the linkee module.
void putModuleMembersInScope(Module* m, Module* linkee) {
  if (!m) return;

  for (Module::iterator it = m->begin(); it != m->end(); ++it) {
    const Function& f = *it;
    
    const string& name = f.getNameStr();
    bool isCxxLinkage = pystring::startswith(name, "_Z", 0);

    bool hasDef = !f.isDeclaration();
    if (hasDef && !isCxxLinkage
               && !pystring::startswith(name, "__cxx_", 0)) {
      globalNames.insert(name);

      // Ensure that, when parsing, function calls to this name will find it
      const Type* ty = f.getType();
      // We get a pointer-to-whatever-function type, because f is a global
      // value (therefore ptr), but we want just the function type.
      if (const PointerType* pty = llvm::dyn_cast<PointerType>(ty)) {
        ty = pty->getElementType();
      }

      if (const llvm::FunctionType* fnty =
                                      llvm::dyn_cast<llvm::FunctionType>(ty)) {
        // Ensure that codegen for the given function finds the 'declare'
        // TODO make lazy prototype?
        Value* decl = linkee->getOrInsertFunction(
            llvm::StringRef(name),
            fnty,
            f.getAttributes());
        /*
        llvm::outs() << "inserting variable in global scope: " << name << " : "
                  << str(fnty) << "\n";
        */
        gScope.insert(name, new foster::SymbolInfo(
                              new VariableAST(name, TypeAST::reconstruct(fnty),
                                              SourceRange::getEmptyRange()),
                              decl));
      } else {
        ASSERT(false) << "how could a function not have function type?!?";
      }
    }
  }
}

string dumpdirFile(const string& filename) {
  static string dumpdir("fc-output/");
  return dumpdir + filename;
}

string dotdirFile(const string& filename) {
  return dumpdirFile("dot/" + filename);
}

void dumpScopesToDotGraphs() {
  ScopedTimer timer("io.dot");
  {
    std::string err;
    llvm::raw_fd_ostream f(dumpdirFile("gScope.dot").c_str(), err);
    if (err.empty()) {
      llvm::WriteGraph(f, &gScope);
    } else {
      foster::EDiag() << "no file to write gScope.dot";
    }
  }

  {
    std::string err;
    llvm::raw_fd_ostream f(dumpdirFile("gTypeScope.dot").c_str(), err);
    if (err.empty()) {
      llvm::WriteGraph(f, &gTypeScope);
    } else {
      foster::EDiag() << "no file to write gTypeScope.dot";
    }
  }
}

void dumpModuleToFile(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.ir");
  string errInfo;
  llvm::raw_fd_ostream LLpreASM(filename.c_str(), errInfo);
  if (errInfo.empty()) {
    LLpreASM << *mod;
  } else {
    llvm::errs() << "Error dumping module to " << filename << "\n";
    llvm::errs() << errInfo << "\n";
    exit(1);
  }
}

void dumpModuleToBitcode(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.bitcode");
  string errInfo;
  sys::RemoveFileOnSignal(sys::Path(filename), &errInfo);

  raw_fd_ostream out(filename.c_str(), errInfo, raw_fd_ostream::F_Binary);
  if (!errInfo.empty()) {
    llvm::errs() << "Error when preparing to write bitcode to " << filename
        << "\n" << errInfo << "\n";
    exit(1);
  }

  WriteBitcodeToFile(mod, out);
}

TargetData* getTargetDataForModule(Module* mod) {
  const string& layout = mod->getDataLayout();
  if (layout.empty()) return NULL;
  return new TargetData(layout);
}

void optimizeModuleAndRunPasses(Module* mod) {
  ScopedTimer timer("llvm.opt");
  PassManager passes;
  FunctionPassManager fpasses(mod);

  TargetData* td = getTargetDataForModule(mod);
  if (td) {
    passes.add(td);
    fpasses.add(new TargetData(*td));
  } else {
    llvm::outs() << "Warning: no target data for module!" << "\n";
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
  for (size_t i = 0; i < cmdLinePassList.size(); ++i) {
    const PassInfo* pi = cmdLinePassList[i];
    llvm::Pass* p = (pi->getNormalCtor()) ? pi->getNormalCtor()() : NULL;
    if (p) {
      passes.add(p);
    } else {
      llvm::errs() << "Error: unable to create LLMV pass "
                << "'" << pi->getPassName() << "'" << "\n";
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

void compileToNativeAssembly(Module* mod, const string& filename) {
  ScopedTimer timer("llvm.llc");

  llvm::Triple triple(mod->getTargetTriple());
  if (triple.getTriple().empty()) {
    triple.setTriple(llvm::sys::getHostTriple());
  }

  const Target* target = NULL;
  string err;
  target = llvm::TargetRegistry::lookupTarget(triple.getTriple(), err);
  if (!target) {
    llvm::errs() << "Error: unable to pick a target for compiling to assembly"
              << "\n";
    exit(1);
  }

  TargetMachine* tm = target->createTargetMachine(triple.getTriple(), "");
  if (!tm) {
    llvm::errs() << "Error! Creation of target machine"
        " failed for triple " << triple.getTriple() << "\n";
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
    llvm::errs() << "Error when opening file to print assembly to:\n\t"
        << err << "\n";
    exit(1);
  }

  llvm::formatted_raw_ostream out(raw_out,
      llvm::formatted_raw_ostream::PRESERVE_STREAM);

  if (tm->addPassesToEmitFile(passes, out,
      TargetMachine::CGFT_AssemblyFile,
      CodeGenOpt::Aggressive,
      disableVerify)) {
    llvm::errs() << "Unable to emit assembly file! " << "\n";
    exit(1);
  }

  passes.doInitialization();
  for (Module::iterator it = mod->begin(); it != mod->end(); ++it) {
    if (it->isDeclaration()) continue;
    passes.run(*it);
  }
  passes.doFinalization();
}

/// Ensures that the given path exists and is a file, not a directory.
void validateInputFile(const string& pathstr) {
  llvm::sys::PathWithStatus path(pathstr);

  if (path.empty()) {
    llvm::errs() << "Error: need an input filename!" << "\n";
    exit(1);
  }

  string err;
  const llvm::sys::FileStatus* status
         = path.getFileStatus(/*forceUpdate=*/ false, &err);
  if (!status) {
    if (err.empty()) {
      llvm::errs() << "Error occurred when reading input path '"
                << pathstr << "'" << "\n";
    } else {
      llvm::errs() << err << "\n";
    }
    exit(1);
  }

  if (status->isDir) {
    llvm::errs() << "Error: input must be a file, not a directory!" << "\n";
    exit(1);
  }
}

void setDefaultCommandLineOptions() {
  if (string(LLVM_HOSTTRIPLE).find("darwin") != string::npos) {
    // Applications on Mac OS X must be compiled with relocatable symbols, which
    // is -mdynamic-no-pic (GCC) or -relocation-model=dynamic-no-pic (llc).
    // Setting the flag here gives us the proper default, while still allowing
    // the user to override via command line options if need be.
    llvm::TargetMachine::setRelocationModel(llvm::Reloc::DynamicNoPIC);
  }

  // Ensure we always compile with -disable-fp-elim
  // to enable simple stack walking for the GC.
  llvm::NoFramePointerElim = true;
}

int main(int argc, char** argv) {
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  foster::linkFosterGC(); // statically, not dynamically
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;

  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");

  setDefaultCommandLineOptions();

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler\n");

  validateInputFile(optInputPath);

  ensureDirectoryExists(dumpdirFile(""));
  ensureDirectoryExists( dotdirFile(""));

  using foster::module;
  using foster::ee;

  foster::initializeLLVM();
  module = new Module("foster", getGlobalContext());
  ee = EngineBuilder(module).create();
  initMaps();

  Module* m = readModuleFromPath("libfoster.bc");
  putModuleMembersInScope(m, module);
  
  createLLVMBitIntrinsics();
  
  llvm::sys::Path inPath(optInputPath);
  const foster::InputFile infile(inPath);
  foster::gInputFile = &infile;

  pANTLR3_BASE_TREE parseTree = NULL;
  foster::ANTLRContext* ctx = NULL;
  unsigned numParseErrors = 0;
  ModuleAST* exprAST = NULL;


  { ScopedTimer timer("io.parse");
    exprAST = foster::parseModule(infile, parseTree, ctx, numParseErrors);
  }
  
  if (optDumpASTs) {
    llvm::outs() << "dumping parse trees" << "\n";
    if (1) {
      std::ofstream out(dumpdirFile("stringtree.dump.txt").c_str());
      out << stringTreeFrom(parseTree) << "\n";
    }

    if (1) {
      foster::pb::Expr pbModuleExpr;

      { ScopedTimer timer("protobuf");
        DumpToProtobufPass p(&pbModuleExpr); exprAST->accept(&p);
      }
      { ScopedTimer timer("protobuf.io");
        std::ofstream out(dumpdirFile("ast.postparse.pb").c_str(),
                              std::ios::trunc | std::ios::binary);
        pbModuleExpr.SerializeToOstream(&out);
      }
    }
  }

  if (numParseErrors > 0) {
    exit(2);
  }

  {
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Adding parent links..." << "\n";
    AddParentLinksPass aplPass; exprAST->accept(&aplPass);
  }
 
  {
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "building CFGs" << "\n";
    { BuildCFG p; exprAST->accept(&p); }
    for (ModuleAST::FnAST_iterator it = exprAST->fn_begin();
           it != exprAST->fn_end(); ++it) {
      FnAST* fnast = *it;
      const string& name = fnast->proto->name;
      string filename(dotdirFile(name + ".dot"));
      if (!fnast->cfgs.empty()) {
        llvm::outs() << "Writing " << filename << "\n";
        std::string err;
        llvm::raw_fd_ostream f(filename.c_str(), err);
        if (err.empty()) { ScopedTimer timer("io.dot");
          llvm::WriteGraph(f, fnast);
        }
      } else {
        foster::EDiag() << "no CFG for " << name;
      }
    }
  }

  {
  llvm::outs() << "=========================" << "\n";
  llvm::outs() << "Type checking... " << "\n";
  }

  { ScopedTimer timer("foster.typecheck");
    TypecheckPass tyPass; exprAST->accept(&tyPass);
  }

  bool sema = exprAST->type != NULL;
  llvm::outs() << "Semantic checking: " << sema << "\n";
  if (!sema) { return 1; }
  
  if (optDumpASTs) { ScopedTimer timer("io.file");
    string outfile = "pp-precc.txt";
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Pretty printing to " << outfile << "\n";
    std::ofstream out(dumpdirFile(outfile).c_str());
    ScopedTimer pptimer("io.prettyprint");
    PrettyPrintPass ppPass(out); exprAST->accept(&ppPass); ppPass.flush();
  }

  {
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Performing closure conversion..." << "\n";
  }

  { ScopedTimer timer("foster.closureconv");
    ClosureConversionPass p(globalNames, exprAST);
    exprAST->accept(&p);
  }

  { ScopedTimer timer("io.file");
    string outfile = "pp-postcc.txt";
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Pretty printing to " << outfile << "\n";
    std::ofstream out(dumpdirFile(outfile).c_str());
    ScopedTimer pptimer("io.prettyprint");
    PrettyPrintPass ppPass(out); exprAST->accept(&ppPass); ppPass.flush();
  }

  llvm::outs() << "=========================" << "\n";

  {
    ScopedTimer timer("foster.codegen");
    CodegenPass cgPass; exprAST->accept(&cgPass);
  }
  
  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module, dumpdirFile("out.prelink.ll").c_str());
  }

  dumpScopesToDotGraphs();

  if (!optCompileSeparately) {
    string errMsg;
    { ScopedTimer timer("llvm.link");
    if (Linker::LinkModules(module, m, &errMsg)) {
      llvm::errs() << "Error when linking modules: " << errMsg << "\n";
    }
    }

    if (optDumpPostLinkedIR) {
      dumpModuleToFile(module, dumpdirFile("out.preopt.ll"));
    }

    optimizeModuleAndRunPasses(module);
    
    if (optDumpPostOptIR) {
      dumpModuleToFile(module, dumpdirFile("out.postopt.ll"));
    }
    
    compileToNativeAssembly(module, dumpdirFile("out.s"));
  } else { // -c, compile to bitcode instead of native assembly
    dumpModuleToBitcode(module, dumpdirFile("out.bc"));
  }
  // TODO invoke g++ .s -> exe

#ifdef LLVM_GE_2_8
  if (optDumpStats) {
    string err;
    llvm::raw_fd_ostream out(dumpdirFile("stats.txt").c_str(), err);
    llvm::PrintStatistics(out);
  }
#endif

  { ScopedTimer timer("protobuf.shutdown");
    google::protobuf::ShutdownProtobufLibrary();
  }
  foster::gInputFile = NULL;
  { ScopedTimer timer("io.file.flush");
    llvm::outs().flush();
    llvm::errs().flush();
  }

  foster::deleteANTLRContext(ctx);
  delete wholeProgramTimer;

  if (optPrintTimings) {
    setTimingDescriptions();
    gTimings.print();
  }
  return 0;
}


