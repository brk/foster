// Copyright (c) 2009-2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/IR/Module.h"
#include "llvm/Linker/Linker.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/DiagnosticPrinter.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Signals.h"

////////////////////////////////////////////////////////////////////

#include "base/Assert.h"
#include "base/LLVMUtils.h"
#include "base/TimingsRepository.h"

#include "passes/FosterPasses.h"
#include "passes/FosterLL.h"

#include "parse/FosterTypeAST.h"
#include "parse/ParsingContext.h" // for LLVM type names

#include "_generated_/FosterIL.capnp.h"

#include <capnp/message.h>
#include <capnp/serialize.h>

#include "StandardPrelude.h"

#include <fstream>

using std::string;

using foster::ScopedTimer;
using foster::EDiag;

using namespace llvm;

static cl::OptionCategory FosterOptCat("Foster-specific Options", "");

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"), cl::cat(FosterOptCat));

// Given -o foo, fosterlower will write foo.preopt.bc
static cl::opt<string>
optOutputName("o",
  cl::desc("Base name of output file"),
  cl::init("out"),
  cl::cat(FosterOptCat));

static cl::opt<string>
optOutdirName("outdir",
  cl::desc("Output directory for output and dump files"),
  cl::init("fc-output"),
  cl::cat(FosterOptCat));

static cl::opt<string>
optBitcodeLibsDir("bitcodelibs",
  cl::desc("Path to _bitcodelibs_ directory"),
  cl::init("_bitcodelibs_"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optEmitDebugInfo("g",
  cl::desc("Emit debug information in generated LLVM IR (not yet implemented)"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optTrackAllocSites("gc-track-alloc-sites",
  cl::desc("Inform the GC of which program locations are allocating"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optCountClosureCalls("count-closure-calls",
  cl::desc("Emit code to count the number of dynamic closure calls made."),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optDisableAllArrayBoundsChecks("unsafe-disable-array-bounds-checks",
  cl::desc("Unsafely omit array bounds checking"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optForceNUW("unsafe-use-nuw",
  cl::desc("Forcibly tag all relevant LLVM instructions with nuw"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optForceNSW("unsafe-use-nsw",
  cl::desc("Forcibly tag all relevant LLVM instructions with nsw"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optDumpPreLinkedIR("dump-prelinked",
  cl::desc("Dump LLVM IR before linking with standard library"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optDumpPostLinkedIR("dump-postlinked",
  cl::desc("Dump LLVM IR after linking with standard library"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optDumpStats("dump-stats",
  cl::desc("Dump timing and other statistics from compilation"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("Print timing measurements of compiler passes"),
  cl::cat(FosterOptCat));

static cl::list<std::string>
linkAgainstBCs("link-against",
  cl::desc("Link against the provided bitcode module(s)"),
  cl::cat(FosterOptCat));

void printVersionInfo(llvm::raw_ostream& out) {
  out << "Foster version: " << FOSTER_VERSION_STR << "\n";
  cl::PrintVersionMessage();
}

void setTimingDescriptions() {
  using foster::gTimings;
  gTimings.describe("total", "Overall compiler runtime");

  gTimings.describe("io.proto", "Time spent parsing input protobuf file");
  gTimings.describe("io.file",  "Time spent doing non-parsing I/O");
  gTimings.describe("io.dot",   "Time spent writing DOT graphs");
  gTimings.describe("io.prettyprint", "Time spent in pretty-printing");

  gTimings.describe("llvm.opt",  "Time spent in LLVM IR optimization");
  gTimings.describe("llvm.link", "Time spent linking LLVM modules");
  gTimings.describe("llvm.llc",  "Time spent doing llc's job (IR->asm)");
}

std::unique_ptr<Module> readLLVMModuleFromPath(string path) {
  foster::validateInputFile(path);
  ScopedTimer timer("io.file.readmodule");
  return foster::readLLVMModuleFromPath(path);
}

string outdirFile(const string& filename) {
  return optOutdirName + "/" + filename;
}

void dumpModuleToFile(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.ir");
  foster::dumpModuleToFile(mod, filename);
}

void dumpModuleToBitcode(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.bitcode");
  foster::dumpModuleToBitcode(mod, filename);
}

void linkTo(std::unique_ptr<llvm::Module> transient,
            const std::string& name,
            llvm::Module& module,
            llvm::Linker::Flags flags = llvm::Linker::Flags::None) {
  bool failed = Linker::linkModules(module, std::move(transient), flags);
  ASSERT(!failed) << "Error when linking in " << name << "\n";
}

namespace foster {
  LLModule* LLModule_from_capnp(const foster::be::Module::Reader&);
}

LLModule* readLLProgramFromCapnp(const string& pathstr) {

  LLModule* prog = NULL;

  { ScopedTimer timer("io.capnp.read+translate");
    FILE* f = fopen(pathstr.c_str(), "rb");
    { int fd = fileno(f);
      ::capnp::ReaderOptions options;
      options.traversalLimitInWords = 128 * 1024 * 1024;
      options.nestingLimit = 128;
      ::capnp::StreamFdMessageReader message(fd, options);
      foster::be::Module::Reader modread = message.getRoot<foster::be::Module>();
      prog = foster::LLModule_from_capnp(modread);
    }
    fclose(f);
  }

  if (!prog) {
    EDiag() << "unable to parse program from LL module protobuf";
    return NULL;
  }
  return prog;
}

bool
areDeclaredValueTypesOK(llvm::Module* mod,
     const std::vector<LLDecl*>& decls) {
  // This function is a sanity check on the LLVM module
  // we'll eventually be linking against. In particular,
  // we want to make sure that any symbols which the program
  // expects to exist are actually available with the
  // expected calling convention (and so forth).
  //
  // The list of declarations to check should not include
  // anything being defined while lowering.
  for (size_t i = 0; i < decls.size(); ++i) {
    LLDecl*   d = decls[i];
    TypeAST*  t = d->getType();
    Function* f = mod->getFunction(d->getName());
    Value* v;
    if (!f) { v = mod->getGlobalVariable(d->getName()); }
    else { // Make sure function callconv matches
      const FnTypeAST* fnty = t->castFnTypeAST();
      ASSERT(fnty) << "found non-function type for " << d->getName()  
                   << "\n\t" << str(t);
      ASSERT(f->getCallingConv() == fnty->getCallingConventionID())
        << "\nCalling convention mismatch for symbol " << d->getName()
        << ":\n"
        << "had " << fnty->getCallingConventionID()
           << "(" << fnty->getCallingConventionName() << ")"
        << "; expected " << f->getCallingConv();
      v = f;
    }

    if (v) {
    ASSERT(v) << "unable to find module entry for " << d->getName();
    llvm::Type* ty = t->getLLVMType();
    if (v->getType() != ty) {
      if (llvm::isa<Constant>(v) && isPointerToType(v->getType(), ty)) {
        // Imported constants should be automatically dereferenced.
        d->autoDeref = true;
      }
      else {
        EDiag() << "mismatch between declared and imported types"
                << " for symbol " << d->getName() << ":\n"
                << "Declared: " << str(t) << "\n"
                << " in LLVM: " << str(ty) << "\n"
                << "Imported: " << str(v->getType()) << "\n";
        return false;
      }
    }
    }

  }
  return true;
}

// Defined in Codegen-coro.cpp
StructTypeAST* getSplitCoroTyp(TypeAST* argTypes);
llvm::StructType* getSplitCoroType(llvm::Type* argTypes);

namespace foster {
  void codegenLL(LLModule*, llvm::Module* mod, CodegenPassConfig config);
}

int main(int argc, char** argv) {
  int program_status = 0;
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;
  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");
  std::unique_ptr<Module> libfoster_bc = NULL;
  std::unique_ptr<Module> coro_bc      = NULL;

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler backend\n");

  foster::validateInputFile(optInputPath + ".cb");

  foster::ensureDirectoryExists(outdirFile(""));

  foster::initializeLLVM();

  std::string mainModulePath = makePathAbsolute(optInputPath);

  foster::ParsingContext::pushNewContext();

  llvm::Module* module = new Module(mainModulePath.c_str(), foster::fosterLLVMContext);

  {
    coro_bc = readLLVMModuleFromPath(optBitcodeLibsDir + "/gc_bc/libfoster_coro.bc");
    linkTo(std::move(coro_bc), "libfoster_coro", *module);
  }

  // TODO mark foster__assert as alwaysinline

  // These are "special" functions in that they need a declaration, but
  // their definition should not be available after linking against libfoster.
  llvm::Type* i32 = foster::builder.getInt32Ty();
  module->getOrInsertFunction("opaquely_i32",
      FunctionType::get(i32, llvm::ArrayRef(i32), /*isVarArg=*/ false));
  llvm::Type* i64 = foster::builder.getInt64Ty();
  module->getOrInsertFunction("opaquely_i64",
      FunctionType::get(i64, llvm::ArrayRef(i64), /*isVarArg=*/ false));

  libfoster_bc = readLLVMModuleFromPath(optBitcodeLibsDir + "/foster_runtime.bc");
  foster::putModuleFunctionsInScope(libfoster_bc.get(), module);

  for (auto arg : linkAgainstBCs) {
    auto bc = readLLVMModuleFromPath(arg);
    linkTo(std::move(bc), arg, *module);
  }

  // The module is "unclean" because it now has types that refer to libfoster_bc;
  // remove the taint by round-tripping to disk. Usually takes ~1ms.
  { ScopedTimer timer("llvm.roundtrip");
    dumpModuleToBitcode(module,     outdirFile(optOutputName + ".stdlib.bc").c_str());
    delete module;
    module = readLLVMModuleFromPath(outdirFile(optOutputName + ".stdlib.bc")).release();
  }
  

  //================================================================
  {
    // Keep synchronized with libfoster_gc_roots.h
    StructTypeAST* coroast = StructTypeAST::getRecursive("foster.coro_ast");
    std::vector<TypeAST*> coro_parts;
    coro_parts.push_back(RefTypeAST::get(TypeAST::i(999)));  // coro ctx
    coro_parts.push_back(RefTypeAST::get(TypeAST::i(999)));  // fn
    coro_parts.push_back(RefTypeAST::get(TypeAST::i(999)));  // env
    coro_parts.push_back(RefTypeAST::get(coroast));          // parent
    coro_parts.push_back(RefTypeAST::get(
                          RefTypeAST::get(coroast)));         // indirect_self
    coro_parts.push_back(TypeAST::i(64)); // effect_tag
    coro_parts.push_back(TypeAST::i(32)); // status
    coroast->setBody(coro_parts);
    foster_generic_coro_ast = coroast;

    foster_generic_coro_t = llvm::StructType::getTypeByName(foster::fosterLLVMContext, "struct.foster_bare_coro");
    // Can't do this yet, because generating type maps requires
    // access to specific coro fields.
    //foster_generic_coro_t = llvm::StructType::create(module->getContext(),
    //                                          "struct.foster_generic_coro");
    ASSERT(foster_generic_coro_t != NULL);

    foster_generic_split_coro_ty = getSplitCoroType(getUnitType()->getLLVMType());

    foster::ParsingContext::insertType("Foster$GenericCoro",
      RefTypeAST::get(getSplitCoroTyp(getUnitType())));
    foster::ParsingContext::insertType("Foster$GenericClosureEnvPtr",
                                      getGenericClosureEnvType());
  }
  //================================================================

  {
    LLModule* prog = readLLProgramFromCapnp(optInputPath + ".cb");
    ASSERT(prog) << "Unable to read LL program from protobuf!";

    if(!areDeclaredValueTypesOK(module, prog->extern_val_decls)) {
      program_status = 1; goto cleanup;
    }

    CodegenPassConfig config;
    config.useNSW            = optForceNSW;
    config.useNUW            = optForceNUW;
    config.trackAllocSites   = optTrackAllocSites;
    config.countClosureCalls = optCountClosureCalls;
    config.disableAllArrayBoundsChecks
                             = optDisableAllArrayBoundsChecks;

    foster::codegenLL(prog, module, config);
  }

  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module,
          outdirFile(optOutputName + ".raw.ll").c_str());
  }

  // Run cleanup passes on newly-generated code,
  // rather than wastefully on post-linked code.
  foster::runCleanupPasses(*module);

  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module,
          outdirFile(optOutputName + ".prelink.ll").c_str());
  }

  { // Run warning passes after dumping prelinked IR so that
    // we can more easily inspect problematic IR.
    foster::runWarningPasses(*module);
  }

  {
    ScopedTimer timer("llvm.link");
    linkTo(std::move(libfoster_bc), "libfoster", *module);
  }

  if (optDumpPostLinkedIR) { // TODO remove this option
    dumpModuleToFile(module, outdirFile(optOutputName + ".preopt.ll"));
  }

  dumpModuleToBitcode(module, outdirFile(optOutputName + ".preopt.bc"));

  if (optDumpStats) {
    std::error_code err;
    llvm::raw_fd_ostream out(outdirFile(optOutputName + "lower.stats.txt").c_str(),
                             err, llvm::sys::fs::OpenFlags::OF_None);
    llvm::PrintStatistics(out);
  }

cleanup:
  foster::gInputFile = NULL;
  llvm::outs().flush();
  llvm::errs().flush();

  foster::ParsingContext::popCurrentContext();

  delete wholeProgramTimer;

  delete module;       module = NULL;

  if (optPrintTimings) {
    setTimingDescriptions();
    foster::gTimings.print("fosterlower");
  }
  return program_status;
}

