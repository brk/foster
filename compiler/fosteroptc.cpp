// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt
#include "llvm/IR/Module.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Config/config.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Target/TargetOptions.h"

#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/TargetTransformInfo.h"

#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/Signals.h"
// #include "llvm/Support/PassNameParser.h"
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

namespace foster {
  void linkFosterGC(); // defined in llmv/plugins/FosterGC.cpp
}

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

void printVersionInfo() {
  llvm::outs() << "Foster version: " << FOSTER_VERSION_STR;
  llvm::outs() << ", compiled: " << __DATE__ << " at " << __TIME__ << "\n";
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
optInsertTimerChecks("foster-insert-timing-checks",
  cl::desc("Insert timing checks at loop backedges"),
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
  gTimings.describe("llvm.llc+", "Time spent doing llc's job (IR->obj) (ms)");
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

// The standard LLVM pass logic migrated from the libraries to opt in 3.0.
// These routines are adapted copies of the ones used by opt.
namespace  {

  void scheduleInternalizePass(PassManagerBase& passes) {
    std::vector<const char*> E;
    E.push_back("foster__runtime__main__wrapper");
    E.push_back("foster__main");
    E.push_back("foster__gcmaps");
    E.push_back("foster_coro_delete_self_reference");
    passes.add(createInternalizePass(E));
  }

  void AddOptimizationPasses(PassManagerBase& MPM,
                             FunctionPassManager& FPM,
                             unsigned OptLevel,
                             bool DisableInline) {
    PassManagerBuilder Builder;
    Builder.OptLevel = OptLevel;

    if (DisableInline) {
      // No inlining pass
    } else if (OptLevel > 1) {
      unsigned Threshold = 225;
      if (OptLevel > 2)
        Threshold = 275;
      Builder.Inliner = createFunctionInliningPass(Threshold);
    } else {
      Builder.Inliner = createAlwaysInlinerPass();
    }
    Builder.DisableUnitAtATime = false;
    Builder.DisableUnrollLoops = OptLevel == 0;

    MPM.add(createVerifierPass());                // Verify that input is correct
    Builder.populateFunctionPassManager(FPM);
    Builder.populateModulePassManager(MPM);
  }

  void PopulateLTOPassManager(PassManagerBuilder& PMB,
  	  	  	      PassManagerBase &PM,
                              bool Internalize,
                              bool RunInliner,
                              bool DisableGVNLoadPRE) {
  // Provide AliasAnalysis services for optimizations.
  //PMB.addInitialAliasAnalysisPasses(PM);
    // Add TypeBasedAliasAnalysis before BasicAliasAnalysis so that
    // BasicAliasAnalysis wins if they disagree. This is intended to help
    // support "obvious" type-punning idioms.
    PM.add(createTypeBasedAliasAnalysisPass());
    PM.add(createBasicAliasAnalysisPass());

  // Now that composite has been compiled, scan through the module, looking
  // for a main function.  If main is defined, mark all other functions
  // internal.
  if (Internalize) {
    scheduleInternalizePass(PM);
  }

  // Propagate constants at call sites into the functions they call.  This
  // opens opportunities for globalopt (and inlining) by substituting function
  // pointers passed as arguments to direct uses of functions.
  PM.add(createIPSCCPPass());

  // Now that we internalized some globals, see if we can hack on them!
  PM.add(createGlobalOptimizerPass());

  // Linking modules together can lead to duplicated global constants, only
  // keep one copy of each constant.
  PM.add(createConstantMergePass());

  // Remove unused arguments from functions.
  PM.add(createDeadArgEliminationPass());

  // Reduce the code after globalopt and ipsccp.  Both can open up significant
  // simplification opportunities, and both can propagate functions through
  // function pointers.  When this happens, we often have to resolve varargs
  // calls, etc, so let instcombine do this.
  PM.add(createInstructionCombiningPass());

  // Inline small functions
  if (RunInliner)
    PM.add(createFunctionInliningPass());

  PM.add(createPruneEHPass());   // Remove dead EH info.

  // Optimize globals again if we ran the inliner.
  if (RunInliner)
    PM.add(createGlobalOptimizerPass());
  PM.add(createGlobalDCEPass()); // Remove dead functions.

  // If we didn't decide to inline a function, check to see if we can
  // transform it to pass arguments by value instead of by reference.
  PM.add(createArgumentPromotionPass());

  // The IPO passes may leave cruft around.  Clean up after them.
  PM.add(createInstructionCombiningPass());
  PM.add(createJumpThreadingPass());
  // Break up allocas
  if (true /*UseNewSROA*/)
    PM.add(createSROAPass());
  else
    PM.add(createScalarReplAggregatesPass());

  // Run a few AA driven optimizations here and now, to cleanup the code.
  PM.add(createFunctionAttrsPass()); // Add nocapture.
  PM.add(createGlobalsModRefPass()); // IP alias analysis.

  PM.add(createLICMPass());                 // Hoist loop invariants.
  PM.add(createGVNPass(DisableGVNLoadPRE)); // Remove redundancies.
  PM.add(createMemCpyOptPass());            // Remove dead memcpys.
  // Nuke dead stores.
  PM.add(createDeadStoreEliminationPass());

  // Cleanup and simplify the code after the scalar optimizations.
  PM.add(createInstructionCombiningPass());

  PM.add(createJumpThreadingPass());

  // Delete basic blocks, which optimization passes may have killed.
  PM.add(createCFGSimplificationPass());

  // Now that we have optimized the program, discard unreachable functions.
  PM.add(createGlobalDCEPass());
}

  void AddStandardLinkPasses(PassManagerBase &PM) {
    PM.add(createVerifierPass());                  // Verify that input is correct
    //PM.add(createStripSymbolsPass(true));
    PassManagerBuilder Builder;
    PopulateLTOPassManager(Builder, PM, /*Internalize=*/ true,
                                        /*RunInliner=*/ true,
                                        /*DisableGVNLoadPRE*/ true);
    //Builder.populateLTOPassManager(PM, /*Internalize=*/ true,
    //                                    /*RunInliner=*/ true);
  }
} // namespace

void optimizeModuleAndRunPasses(Module* mod) {
  ScopedTimer timer("llvm.opt");
  PassManager passes;
  FunctionPassManager fpasses(mod);

  { PassManager passes_first;
    passes_first.add(llvm::createVerifierPass());
    passes_first.run(*mod);
  }

  if (!optNoSpecializeMemallocs) {
    ScopedTimer timer("llvm.opt.memalloc");
    FunctionPassManager fpasses_first(mod);
    // Run this one before inlining, otherwise we won't see the mallocs!
    fpasses_first.add(foster::createMemallocSpecializerPass());
    foster::runFunctionPassesOverModule(fpasses_first, mod);
  }

  if (!optOptimizeZero) {
    AddOptimizationPasses(passes, fpasses, 2, false);
    AddStandardLinkPasses(passes);

    if (!optNoCoalesceLoads) {
      fpasses.add(foster::createBitcastLoadRecognizerPass());
    }
  }

  /*
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
  */

  if (optInsertTimerChecks) {
    fpasses.add(new llvm::LoopInfoWrapperPass());
    fpasses.add(foster::createTimerChecksInsertionPass());
  }

  if (!optOptimizeZero) {
    AddOptimizationPasses(passes, fpasses, 3, false);
    passes.add(llvm::createVerifierPass());
  }

  foster::runFunctionPassesOverModule(fpasses, mod);
  passes.run(*mod);
}

void runInternalizePasses(Module* mod) {
  ScopedTimer timer("llvm.opt");
  PassManager passes;
  PassManagerBuilder Builder;
  scheduleInternalizePass(passes);
  passes.add(createGlobalDCEPass());
  passes.run(*mod);
}

llvm::sys::fs::OpenFlags
fdFlagsForObjectType(TargetMachine::CodeGenFileType filetype) {
  if (filetype == TargetMachine::CGFT_ObjectFile) {
    return llvm::sys::fs::OpenFlags::F_None;
  }
  return llvm::sys::fs::OpenFlags::F_Text;
}

#if defined(LLVM_HOSTTRIPLE)
std::string HOST_TRIPLE = LLVM_HOSTTRIPLE;
#elif defined(LLVM_DEFAULT_TARGET_TRIPLE)
std::string HOST_TRIPLE = LLVM_DEFAULT_TARGET_TRIPLE;
#else
#error Unable to determine host triple!
#endif

llvm::Reloc::Model relocModel = llvm::Reloc::Default;

void configureTargetDependentOptions(const llvm::Triple& triple,
                                     llvm::TargetOptions& targetOptions,
                                     TargetMachine::CodeGenFileType filetype) {
  if (triple.isMacOSX()) {
    // Applications on Mac OS X (x86) must be compiled with relocatable symbols,
    // which is -mdynamic-no-pic (GCC) or -relocation-model=dynamic-no-pic (llc).
    relocModel = llvm::Reloc::DynamicNoPIC;
  }
}

void compileToNativeAssemblyOrObject(Module* mod, const string& filename) {
  auto filetype = TargetMachine::CGFT_ObjectFile;
  if (pystring::endswith(filename, ".s")) {
    filetype = TargetMachine::CGFT_AssemblyFile;
  } else if (pystring::endswith(filename, ".o")
         || pystring::endswith(filename, ".obj")) {
    filetype = TargetMachine::CGFT_ObjectFile;
  } else {
    ASSERT(false) << "Expected filename " << filename
                  << " to end with .s or .o or .obj";
  }

  ScopedTimer timer((filetype == TargetMachine::CGFT_AssemblyFile) ? "llvm.llc"
                   :(filetype == TargetMachine::CGFT_ObjectFile)   ? "llvm.llc+"
                                                                   : "llvm.llc?");

  llvm::Triple triple(mod->getTargetTriple());
  if (triple.getTriple().empty()) {
    triple.setTriple(HOST_TRIPLE);
  }
  auto targetOptions = new llvm::TargetOptions();
  configureTargetDependentOptions(triple, *targetOptions, filetype);

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

  auto cgModel = CodeModel::Default;
  auto tm = target->createTargetMachine(triple.getTriple(),
                                                 "", // CPU
                                                 "", // Features
                                                 *targetOptions,
                                                 relocModel,
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

  PassManager passes;
  passes.add(createTargetTransformInfoWrapperPass(tm->getTargetIRAnalysis()));

  std::error_code err;
  llvm::raw_fd_ostream out(filename.c_str(), err,
                           fdFlagsForObjectType(filetype));
  ASSERT(!err) << "Error when opening file to print output to: " << filename;

  bool disableVerify = true;
  if (tm->addPassesToEmitFile(passes, out, filetype,
#ifndef LLVM_DEFAULT_TARGET_TRIPLE
                              cgOptLevel,
#endif
                              disableVerify)) {
    llvm::errs() << "Unable to emit assembly file! " << "\n";
    exit(1);
  }

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
  foster::linkFosterGC(); // statically, not dynamically
  sys::PrintStackTraceOnErrorSignal();
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
                             err, llvm::sys::fs::OpenFlags::F_None);
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

