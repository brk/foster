// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
#include "llvm/IR/Module.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/CodeGen/CommandFlags.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Target/TargetOptions.h"

#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"

#include "llvm/Transforms/IPO/Internalize.h"
#include "llvm/Transforms/IPO/GlobalDCE.h"

#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"

#include "llvm/Support/FileSystem.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"

#include "base/Assert.h"
#include "base/LLVMUtils.h"
#include "base/TimingsRepository.h"

#include "passes/FosterPasses.h"

#include "pystring/pystring.h"

#include <fstream>

using namespace llvm;
using namespace llvm::legacy;

using foster::ScopedTimer;
using foster::SourceRange;
using foster::EDiag;

using std::string;

void printUsage () {
  llvm::raw_ostream& o = llvm::outs();
  o << "Synopsis:";
  o << "\n  fosteroptc <input> <out.{s,o,obj}>";
  o << "\n        runs optimization passes and emits native code";
  o << "\n                                      -cleanup-only";
  o << "\n        runs cleanup and warning LLVM passes, but";
  o << "\n        does not run any optimizations or emit any native code.";
  o << "\n";
}

void printVersionInfo(llvm::raw_ostream& out) {
  out << "Foster version: " << FOSTER_VERSION_STR << "\n";
  cl::PrintVersionMessage();
}

const char kDefaultOutputExtension[] = ".s";

static cl::OptionCategory FosterOptCat("Foster-specific Options", "");

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file.bc/ll>"), cl::cat(FosterOptCat));

static cl::opt<string>
optOutputName("o",
  cl::desc("Output file, with optional extension {s,o,obj}, default 's'"),
  cl::cat(FosterOptCat));

static string gOutputNameBase;

static cl::opt<bool>
optDumpPreOptIR("dump-preopt",
  cl::desc("Dump LLVM IR before linking and optimization passes"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optDumpPostOptIR("dump-postopt",
  cl::desc("Dump LLVM IR after linking and optimization passes"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optCleanupOnly("cleanup-only",
  cl::desc("Run cleanup passes only"),
  cl::cat(FosterOptCat),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optInternalize("foster-internalize",
  cl::desc("Internalize and strip unreferenced globals"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optInsertTimerChecks("foster-insert-timer-checks",
  cl::desc("Insert timer flag checks at loop backedges"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optDumpStats("dump-stats",
  cl::desc("Dump timing and other statistics from compilation"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("Print timing measurements of compiler passes"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optOptimizeZero("O0",
  cl::desc("Disable most optimization passes after linking with standard library"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optDisableAllOptimizations("Onone",
  cl::desc("Disable all optimization passes after linking with standard library"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optNoInline("no-inline",
  cl::desc("Disable inlining"),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optNoSpecializeMemallocs("no-specialize-memallocs",
  cl::desc("Disable specialization of memallocs of common sizes."),
  cl::cat(FosterOptCat));

static cl::opt<bool>
optNoCoalesceLoads("no-coalesce-loads",
  cl::desc("Disable coalescing loads of bit-or'ed values."),
  cl::cat(FosterOptCat));

/*
static cl::list<const PassInfo*, bool, PassNameParser>
cmdLinePassList(cl::desc("Optimizations available:"),
  cl::cat(FosterOptCat));
*/

static llvm::codegen::RegisterCodeGenFlags rcgf;

void setTimingDescriptions() {
  using foster::gTimings;
  gTimings.describe("total", "Overall compiler runtime");

  gTimings.describe("io.parse", "Time spent parsing input file");
  gTimings.describe("io.file",  "Time spent doing non-parsing I/O");
  gTimings.describe("io.dot",   "Time spent writing DOT graphs");
  gTimings.describe("io.prettyprint", "Time spent in pretty-printing");

  gTimings.describe("llvm.opt",  "Time spent in LLVM IR optimization");
  gTimings.describe("llvm.link", "Time spent linking LLVM modules");
  gTimings.describe("llvm.llc",  "Time spent doing llc's job (IR->asm)");
  gTimings.describe("llvm.llc+", "Time spent doing llc's job (IR->obj)");
}

Module* readLLVMModuleFromPath(string path) {
  foster::validateInputFile(path);
  ScopedTimer timer("io.file.readmodule");
  Module* module = foster::readLLVMModuleFromPath(path).release();
  ASSERT(module != NULL);
  return module;
}

void dumpModuleToFile(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.ir");
  foster::dumpModuleToFile(mod, filename);
}

void dumpModuleToBitcode(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.bitcode");
  foster::dumpModuleToBitcode(mod, filename);
}



void applyColdCC(const std::string& name, Module* mod) {
  llvm::Function* write_barrier_slowpath = mod->getFunction(name);
  if (write_barrier_slowpath) {
    write_barrier_slowpath->setCallingConv(llvm::CallingConv::Cold);
    for (auto it : write_barrier_slowpath->users()) {
      if (auto call = dyn_cast<llvm::CallInst>(it)) {
        call->setCallingConv(llvm::CallingConv::Cold);
      }
    }
  }
}

void optimizeModuleAndRunPasses(Module* mod) {
  ScopedTimer timer("llvm.opt");
  legacy::PassManager passes;
  legacy::FunctionPassManager fpasses(mod);

  // Forcibly inline our barriers now that barrier optimizations have been run.
  std::vector<std::string> barriers = {
    "foster_write_barrier_with_obj_generic",
    "foster_read_pseudobarrier"
  };
  for (const auto& name : barriers) {
    auto barrier = mod->getFunction(name);
    if (barrier) {
      bool wasOptNone = barrier->hasFnAttribute(Attribute::OptimizeNone);
      if (!wasOptNone) {
        // OptNone requires NoInline
        mod->getFunction(name)->removeFnAttr(Attribute::NoInline);
        mod->getFunction(name)->addFnAttr(Attribute::AlwaysInline);
      }
    }
  }

  // Mark our write barrier slowpath with the "cold" calling convention,
  // to minimize instances of register clobbering on the fast path.
  applyColdCC("foster_write_barrier_with_obj_fullpath", mod);
  
  llvm::verifyModule(*mod, &errs());

  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;


  llvm::PassBuilder PB;

  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  llvm::ModulePassManager MPM;

  if (!optNoSpecializeMemallocs) {
    foster::addMemallocSpecializerPass(MPM);
  }

  if (!optOptimizeZero) {
    MPM.addPass(PB.buildPerModuleDefaultPipeline(OptimizationLevel::O2));
  }

  if (optInsertTimerChecks) {
    foster::addTimerChecksInsertionPass(MPM);
  }

  if (!optOptimizeZero) {
    PB.buildPerModuleDefaultPipeline(OptimizationLevel::O3);
    MPM.addPass(llvm::VerifierPass());
  }

    MPM.run(*mod, MAM);

  verifyModule(*mod, &errs());
}

void runInternalizePasses(Module* mod) {
  ScopedTimer timer("llvm.opt");

  auto PreserveThese = [=](const GlobalValue& GV) {
    return GV.getName() == "foster__runtime__main__wrapper"
        || GV.getName() == "foster__main"
        || GV.getName() == "foster_coro_delete_self_reference";
  };
  llvm::internalizeModule(*mod, PreserveThese);

  llvm::ModulePassManager MPM;
  MPM.addPass(GlobalDCEPass());
  llvm::ModuleAnalysisManager MAM;
  MPM.run(*mod, MAM);
}

llvm::sys::fs::OpenFlags
fdFlagsForObjectType(CodeGenFileType filetype) {
  if (filetype == CGFT_ObjectFile) {
    return llvm::sys::fs::OpenFlags::OF_None;
  }
  return llvm::sys::fs::OpenFlags::OF_Text;
}

#if defined(LLVM_HOSTTRIPLE)
std::string HOST_TRIPLE = LLVM_HOSTTRIPLE;
#elif defined(LLVM_DEFAULT_TARGET_TRIPLE)
std::string HOST_TRIPLE = LLVM_DEFAULT_TARGET_TRIPLE;
#else
#error Unable to determine host triple!
#endif

void compileToNativeAssemblyOrObject(Module* mod, const string& filename) {
  auto filetype = CGFT_ObjectFile;
  if (pystring::endswith(filename, ".s")) {
    filetype = CGFT_AssemblyFile;
  } else if (pystring::endswith(filename, ".o")
         || pystring::endswith(filename, ".obj")) {
    filetype = CGFT_ObjectFile;
  } else {
    ASSERT(false) << "Expected filename " << filename
                  << " to end with .s or .o or .obj";
  }

  ScopedTimer timer((filetype == CGFT_AssemblyFile) ? "llvm.llc"
                   :(filetype == CGFT_ObjectFile)   ? "llvm.llc+"
                                                    : "llvm.llc?");

  llvm::Triple triple(mod->getTargetTriple());
  if (triple.getTriple().empty()) {
    triple.setTriple(HOST_TRIPLE);
  }
  auto targetOptions = llvm::codegen::InitTargetOptionsFromCodeGenFlags(triple);

  const Target* target = NULL;
  string errstr;
  target = llvm::TargetRegistry::lookupTarget(triple.getTriple(), errstr);
  if (!target) {
    llvm::errs() << "Error: unable to pick a target for compiling to assembly"
              << "\n";
    exit(1);
  }

  auto cgOptLevel = optOptimizeZero
                        ? CodeGenOpt::None
                        : CodeGenOpt::Aggressive;

  std::optional<CodeModel::Model> cgModel = std::nullopt;
  auto tm = target->createTargetMachine(
                triple.getTriple(),
                "", // CPU
                "", // Features
                targetOptions,
                llvm::codegen::getRelocModel(),
                cgModel
#ifdef LLVM_DEFAULT_TARGET_TRIPLE
                , cgOptLevel
#endif
                );
  if (!tm) {
    llvm::errs() << "Error! Creation of target machine"
        " failed for triple " << triple.getTriple() << "\n";
    exit(1);
  }

  tm->Options.MCOptions.AsmVerbose = true;

  std::error_code err;
  llvm::raw_fd_ostream out(filename.c_str(), err,
                           fdFlagsForObjectType(filetype));
  ASSERT(!err) << "Error when opening file to print output to: " << filename;

  TargetLibraryInfoImpl TLII(triple);

  legacy::PassManager passes;
  passes.add(new TargetLibraryInfoWrapperPass(TLII));
  passes.add(createTargetTransformInfoWrapperPass(tm->getTargetIRAnalysis()));
  if (!optNoInline) {
    passes.add(createAlwaysInlinerLegacyPass());
  }

  bool disableVerify = true;
  auto dwarfObjectOut = nullptr;
  if (tm->addPassesToEmitFile(passes, out, dwarfObjectOut, filetype,
#ifndef LLVM_DEFAULT_TARGET_TRIPLE
                              cgOptLevel,
#endif
                              disableVerify)) {
    llvm::errs() << "Unable to emit assembly file! " << "\n";
    exit(1);
  }

  mod->setDataLayout(tm->createDataLayout());

  passes.run(*mod);
}

// Postcondition: gOuptutNameBase is the output name with no extension;
//                  optOuptutName is the output name with extension.
void calculateOutputNames() {
  ASSERT(optOutputName != "");

  if ( pystring::endswith(optOutputName, ".o")
    || pystring::endswith(optOutputName, ".s")) {
    gOutputNameBase = string(optOutputName.begin(), optOutputName.end() - 2);
  } else if (pystring::endswith(optOutputName, ".obj")) {
    gOutputNameBase = string(optOutputName.begin(), optOutputName.end() - 4);
  } else {
    gOutputNameBase = optOutputName;
    optOutputName = optOutputName + kDefaultOutputExtension;
  }
}

int main(int argc, char** argv) {
  int program_status = 0;
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler backend (LLVM optimization)\n");

  if (optOutputName == "") {
    printUsage();
    return 1;
  }

  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");
  foster::initializeLLVM();
  calculateOutputNames();

  auto mainModulePath = makePathAbsolute(optInputPath);
  llvm::errs() << "reading " << mainModulePath << "\n";
  llvm::Module* module = readLLVMModuleFromPath(mainModulePath);

  if (optCleanupOnly) {
    foster::runCleanupPasses(*module);
    dumpModuleToBitcode(module, (gOutputNameBase + ".cleaned.bc"));
    foster::runWarningPasses(*module);
  } else if (optInternalize) {
    runInternalizePasses(module);
    dumpModuleToFile(module,  (gOutputNameBase + ".internalized.ll"));
  } else {
    if (optDumpPreOptIR) {
      dumpModuleToFile(module,  (gOutputNameBase + ".preopt.ll"));
    }

    if (!optDisableAllOptimizations) {
      foster::runWarningPasses(*module);
      optimizeModuleAndRunPasses(module);

      if (optDumpPostOptIR) {
        dumpModuleToFile(module,  (gOutputNameBase + ".postopt.ll"));
      }
    }

    compileToNativeAssemblyOrObject(module, optOutputName);
  }

  if (optDumpStats) {
    std::error_code err;
    llvm::raw_fd_ostream out((gOutputNameBase + ".optc.stats.txt").c_str(),
                             err, llvm::sys::fs::OpenFlags::OF_None);
    llvm::PrintStatistics(out);
  }

  llvm::outs().flush();
  llvm::errs().flush();

  delete wholeProgramTimer;

  delete module; module = NULL;

  if (optPrintTimings) {
    setTimingDescriptions();
    foster::gTimings.print("fosteroptc");
  }
  return program_status;
}

