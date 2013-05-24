// Copyright (c) 2009-2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Module.h"
#include "llvm/Linker.h"
#include "llvm/ADT/Statistic.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Signals.h"

////////////////////////////////////////////////////////////////////

#include "base/Assert.h"
#include "base/LLVMUtils.h"
#include "base/TimingsRepository.h"

#include "passes/FosterPasses.h"
#include "passes/FosterLL.h"

#include "parse/FosterTypeAST.h"
#include "parse/ProtobufToLLExpr.h"
#include "parse/ParsingContext.h" // for LLVM type names

#include "_generated_/FosterIL.pb.h"

#include "StandardPrelude.h"

#include <fstream>

using std::string;

using foster::ScopedTimer;
using foster::EDiag;

namespace foster {
  extern bool gPrintLLVMImports; // in StandardPrelude.cpp
}

using namespace llvm;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

// Given -o foo, fosterlower will write foo.preopt.bc
static cl::opt<string>
optOutputName("o",
  cl::desc("[foster] Base name of output file"),
  cl::init("out"));

static cl::opt<string>
optOutdirName("outdir",
  cl::desc("[foster] Output directory for output and dump files"),
  cl::init("fc-output"));

static cl::opt<string>
optBitcodeLibsDir("bitcodelibs",
  cl::desc("[foster] Path to _bitcodelibs_ directory"),
  cl::init("_bitcodelibs_"));

static cl::opt<bool>
optEmitDebugInfo("g",
  cl::desc("[foster] Emit debug information in generated LLVM IR"));

static cl::opt<bool>
optTrackAllocSites("gc-track-alloc-sites",
  cl::desc("[foster] Inform the GC of which program locations are allocating"));

static cl::opt<bool>
optDontKillDeadSlots("dont-kill-dead-slots",
  cl::desc("[foster] Disable nulling-out of statically dead GC root slots"));

// Note: bootstrap/testcases/lifetime-no-inline-crash fails when run thusly:
//   ./gotest.sh bootstrap/testcases/lifetime-no-inline-crash -I ../stdlib --me-arg=--no-inline --optimize=O2 --asm --be-arg=--enable-lifetime-info
// I haven't yet figured out whether we are generating subtly incorrect lifetime
// markers (likely), or whether LLVM 3.2 is incorrectly inlining our lifetime
// markers (unlikely). TODO create an independent testcase based on out.preopt.ll
// with no dependency on libfoster to attempt to narrow down the problem.
//
// Anyways, we default to not doing anything with lifetime info because
// the middle-end already reuses gc slots, and I don't think LLVM reuses
// gcroot-marked stack slots, even with lifetime info enabled.
//
// Also note that even if lifetime info is disabled, we can still use the
// generated markers to emit explicit stores for killing dead stack slots.
static cl::opt<bool>
optEnableLifetimeInfo("enable-lifetime-info",
  cl::desc("[foster] Enable lifetime info for GC roots"));

static cl::opt<bool>
optDisableAllArrayBoundsChecks("unsafe-disable-array-bounds-checks",
  cl::desc("[foster] Unsafely omit array bounds checking"));
static cl::opt<bool>
optForceNUW("unsafe-use-nuw",
  cl::desc("[foster] Forcibly tag all relevant LLVM instructions with nuw"));

static cl::opt<bool>
optForceNSW("unsafe-use-nsw",
  cl::desc("[foster] Forcibly tag all relevant LLVM instructions with nsw"));

static cl::opt<bool>
optDisableGC("unsafe-disable-gc",
  cl::desc("[foster] Disable all GC-related code generation (UNSAFE!)"));

static cl::opt<bool>
optDumpPreLinkedIR("dump-prelinked",
  cl::desc("[foster] Dump LLVM IR before linking with standard library"));

static cl::opt<bool>
optDumpPostLinkedIR("dump-postlinked",
  cl::desc("[foster] Dump LLVM IR after linking with standard library"));

static cl::opt<bool>
optDumpStats("dump-stats",
  cl::desc("[foster] Dump timing and other statistics from compilation"));

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("[foster] Print timing measurements of compiler passes"));

static cl::opt<bool>
optPrintLLVMImports("foster-print-llvm-imports",
  cl::desc("[foster] Print imported symbols from imported LLVM modules"));

void printVersionInfo() {
  llvm::outs() << "Foster version: " << FOSTER_VERSION_STR;
  llvm::outs() << ", compiled: " << __DATE__ << " at " << __TIME__ << "\n";
  cl::PrintVersionMessage();
}

void setTimingDescriptions() {
  using foster::gTimings;
  gTimings.describe("total", "Overall compiler runtime (ms)");

  gTimings.describe("io.parse", "Time spent parsing input file (ms)");
  gTimings.describe("io.file",  "Time spent doing non-parsing I/O (ms)");
  gTimings.describe("io.dot",   "Time spent writing DOT graphs (ms)");
  gTimings.describe("io.prettyprint", "Time spent in pretty-printing (ms)");

  gTimings.describe("llvm.opt",  "Time spent in LLVM IR optimization (ms)");
  gTimings.describe("llvm.link", "Time spent linking LLVM modules (ms)");
  gTimings.describe("llvm.llc",  "Time spent doing llc's job (IR->asm) (ms)");
}

Module* readLLVMModuleFromPath(string path) {
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

void linkTo(llvm::Module*& transient,
            const std::string& name,
            llvm::Module* module) {
  string errMsg;
  bool failed = Linker::LinkModules(module, transient, llvm::Linker::DestroySource, &errMsg);
  ASSERT(!failed) << "Error when linking in " << name << ": " << errMsg << "\n";
}

LLModule* readLLProgramFromProtobuf(const string& pathstr,
                                   foster::bepb::Module& out_sm) {
  std::fstream input(pathstr.c_str(), std::ios::in | std::ios::binary);
  if (!out_sm.ParseFromIstream(&input)) {
    EDiag() << "ParseFromIstream() failed!";
    return NULL;
  }

  //const foster::InputTextBuffer* inputBuffer = gInputTextBuffer;
  //gInputTextBuffer = newInputBufferFromSourceModule(out_sm);

  LLModule* prog = foster::LLModule_from_pb(out_sm);
  //gInputTextBuffer = inputBuffer;

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
      ASSERT(fnty);
      ASSERT(f->getCallingConv() == fnty->getCallingConventionID())
        << "\nCalling convention mismatch for symbol " << d->getName()
        << ":\n"
        << "had " << fnty->getCallingConventionID()
           << "(" << fnty->getCallingConventionName() << ")"
        << "; expected " << f->getCallingConv();
      v = f;
    }

    ASSERT(v) << "unable to find module entry for " << d->getName();
    llvm::Type* ty = t->getLLVMType();
    if (v->getType() != ty) {
      EDiag() << "mismatch between declared and imported types"
              << " for symbol " << d->getName() << ":\n"
              << "Declared: " << str(t) << "\n"
              << " in LLVM: " << str(ty) << "\n"
              << "Imported: " << str(v->getType()) << "\n";
      return false;
    }

  }
  return true;
}

namespace foster {
  void codegenLL(LLModule*, llvm::Module* mod, CodegenPassConfig config);
}

int main(int argc, char** argv) {
  int program_status = 0;
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;
  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");
  Module* libfoster_bc = NULL;
  Module* imath_bc     = NULL;
  Module* coro_bc      = NULL;
  //llvm::Type* mp_int = NULL;
  foster::bepb::Module pbin;

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler backend\n");

  foster::gPrintLLVMImports = optPrintLLVMImports;
  foster::validateInputFile(optInputPath);

  foster::ensureDirectoryExists(outdirFile(""));

  foster::initializeLLVM();

  llvm::sys::Path mainModulePath(optInputPath);
  makePathAbsolute(mainModulePath);

  foster::ParsingContext::pushNewContext();

  llvm::Module* module = new Module(mainModulePath.str().c_str(), getGlobalContext());

  {
    coro_bc = readLLVMModuleFromPath(optBitcodeLibsDir + "/gc_bc/libfoster_coro.bc");
    linkTo(coro_bc, "libfoster_coro", module);

    StructTypeAST* coroast = StructTypeAST::getRecursive("foster_generic_coro.struct");
    std::vector<TypeAST*> coro_parts;
    coro_parts.push_back(RefTypeAST::get(TypeAST::i(999)));  // coro ctx
    coro_parts.push_back(RefTypeAST::get(coroast));          // sibling
    coro_parts.push_back(RefTypeAST::get(TypeAST::i(999)));  // fn
    coro_parts.push_back(RefTypeAST::get(TypeAST::i(999)));  // env
    coro_parts.push_back(RefTypeAST::get(coroast));          // invoker
    coro_parts.push_back(RefTypeAST::get(
                         RefTypeAST::get(coroast)));         // indirect_self
    coro_parts.push_back(TypeAST::i(32)); // status
    coroast->setBody(coro_parts);
    foster_generic_coro_ast = coroast;

    foster_generic_coro_t = module->getTypeByName("struct.foster_generic_coro");
    // Can't do this yet, because generating type maps requires
    // access to specific coro fields.
    //foster_generic_coro_t = llvm::StructType::create(module->getContext(),
    //                                          "struct.foster_generic_coro");
    ASSERT(foster_generic_coro_t != NULL);
  }

  // TODO mark foster__assert as alwaysinline
  {
    // This is a "special" function in that it needs a declaration but
    // no definition available after linking against libfoster.
    llvm::Type* i32 = foster::builder.getInt32Ty();
    module->getOrInsertFunction("opaquely_i32",
        FunctionType::get(i32, llvm::makeArrayRef(i32), /*isVarArg=*/ false)
      );
  }

  libfoster_bc = readLLVMModuleFromPath(optBitcodeLibsDir + "/foster_runtime.bc");
  foster::putModuleFunctionsInScope(libfoster_bc, module);

  //================================================================
  foster::ParsingContext::insertType("Foster$GenericClosureEnvPtr",
                                     getGenericClosureEnvType());
  //================================================================

  {
    LLModule* prog = readLLProgramFromProtobuf(optInputPath, pbin);
    ASSERT(prog) << "Unable to read LL program from protobuf!";

    if(!areDeclaredValueTypesOK(module, prog->extern_val_decls)) {
      program_status = 1; goto cleanup;
    }

    CodegenPassConfig config;
    config.useGC             = !optDisableGC;
    config.useNSW            = optForceNSW;
    config.useNUW            = optForceNUW;
    config.trackAllocSites   = optTrackAllocSites;
    config.killDeadSlots     = !optDontKillDeadSlots;
    config.emitLifetimeInfo  = optEnableLifetimeInfo;
    config.disableAllArrayBoundsChecks
                             =  optDisableAllArrayBoundsChecks;

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

  { ScopedTimer timer("llvm.link");
    linkTo(libfoster_bc, "libfoster", module);
    //linkTo(imath_bc,     "imath",     module);
  }

  if (optDumpPostLinkedIR) {
    dumpModuleToFile(module, outdirFile(optOutputName + ".preopt.ll"));
  }

  dumpModuleToBitcode(module, outdirFile(optOutputName + ".preopt.bc"));

  if (optDumpStats) {
    string err;
    llvm::raw_fd_ostream out(outdirFile(optOutputName + "lower.stats.txt").c_str(), err);
    llvm::PrintStatistics(out);
  }

cleanup:
  google::protobuf::ShutdownProtobufLibrary();
  foster::gInputFile = NULL;
  llvm::outs().flush();
  llvm::errs().flush();

  foster::ParsingContext::popCurrentContext();

  delete wholeProgramTimer;

  delete coro_bc;      coro_bc = NULL;
  delete libfoster_bc; libfoster_bc = NULL;
  delete imath_bc;     imath_bc = NULL;
  delete module;       module = NULL;

  if (optPrintTimings) {
    setTimingDescriptions();
    foster::gTimings.print("fosterlower");
  }
  return program_status;
}

