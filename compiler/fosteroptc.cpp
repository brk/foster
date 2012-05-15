// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Module.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/PassManager.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Config/config.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Target/TargetOptions.h"

#include "llvm/DefaultPasses.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Support/Host.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/PassNameParser.h"
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

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file.bc/ll>"));

static cl::opt<string>
optOutputName("o",
  cl::desc("[foster] Output file, with optional extension {s,o,obj}, default 's'"));

static string gOutputNameBase;

static cl::opt<bool>
optDumpPostOptIR("dump-postopt",
  cl::desc("[foster] Dump LLVM IR after linking and optimization passes"));

static cl::opt<bool>
optCleanupOnly("cleanup-only",
  cl::desc("[foster] Run cleanup passes only"));

static cl::opt<bool>
optDumpStats("dump-stats",
  cl::desc("[foster] Dump timing and other statistics from compilation"));

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("[foster] Print timing measurements of compiler passes"));

static cl::opt<bool>
optOptimizeZero("O0",
  cl::desc("[foster] Disable optimization passes after linking with standard library"));

static cl::opt<bool>
optNoSpecializeMemallocs("no-specialize-memallocs",
  cl::desc("[foster] Disable specialization of memallocs of common sizes."));

static cl::opt<string>
optCFI("fosterc-cfi",
  cl::desc("[foster] CFI directives: {yes,no}, default to platform-specific behavior"));

static cl::list<const PassInfo*, bool, PassNameParser>
cmdLinePassList(cl::desc("Optimizations available:"));

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
  Module* module = foster::readLLVMModuleFromPath(path);
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
    Builder.DisableSimplifyLibCalls = false;

    MPM.add(createVerifierPass());                // Verify that input is correct
    Builder.populateFunctionPassManager(FPM);
    Builder.populateModulePassManager(MPM);
  }

  void AddStandardLinkPasses(PassManagerBase &PM) {
    PM.add(createVerifierPass());                  // Verify that input is correct
    //PM.add(createStripSymbolsPass(true));
    PassManagerBuilder Builder;
    Builder.populateLTOPassManager(PM, /*Internalize=*/ true,
                                        /*RunInliner=*/ true);
  }
} // namespace

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

  { PassManager passes_first;
    passes_first.add(llvm::createVerifierPass());
    passes_first.run(*mod);
  }

  if (!optNoSpecializeMemallocs) {
    ScopedTimer timer("llvm.opt.memalloc");
    FunctionPassManager fpasses_first(mod);
    // Run this one before inlining, otherwise we won't see the mallocs!
    fpasses_first.add(new TargetData(*td));
    fpasses_first.add(foster::createMemallocSpecializerPass());
    foster::runFunctionPassesOverModule(fpasses_first, mod);
  }

  if (!optOptimizeZero) {
    AddOptimizationPasses(passes, fpasses, 2, false);
    AddStandardLinkPasses(passes);
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
    AddOptimizationPasses(passes, fpasses, 3, false);
    passes.add(llvm::createVerifierPass());
  }

  foster::runFunctionPassesOverModule(fpasses, mod);
  passes.run(*mod);
}

int fdFlagsForObjectType(TargetMachine::CodeGenFileType filetype) {
  int flags = 0;
  if (filetype == TargetMachine::CGFT_ObjectFile) {
    flags |= raw_fd_ostream::F_Binary;
  }
  return flags;
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
                                     TargetMachine::CodeGenFileType filetype) {
  if (triple.isMacOSX()) {
    // Applications on Mac OS X (x86) must be compiled with relocatable symbols,
    // which is -mdynamic-no-pic (GCC) or -relocation-model=dynamic-no-pic (llc).
    relocModel = llvm::Reloc::DynamicNoPIC;

    if (optCFI.empty() && filetype == TargetMachine::CGFT_AssemblyFile) {
      // Mac OS X system assembler doesn't support .cfi directives yet
      optCFI = "no";
    }
  }

  // Ensure we always compile with -disable-fp-elim
  // to enable simple stack walking for the GC.
  llvm::NoFramePointerElim = true;
}

void compileToNativeAssemblyOrObject(Module* mod, const string& filename) {
  TargetMachine::CodeGenFileType filetype = TargetMachine::CGFT_ObjectFile;
  if (pystring::endswith(filename, ".s")) {
    filetype = TargetMachine::CGFT_AssemblyFile;
  } else if (pystring::endswith(filename, ".o")
         || pystring::endswith(filename, ".obj")) {
    filetype = TargetMachine::CGFT_ObjectFile;
  } else {
    ASSERT(false) << "Expected filename " << filename
                  << " to end with .s or .o or .obj";
  }

  ScopedTimer timer((filetype == TargetMachine::CGFT_AssemblyFile)
                    ? "llvm.llc" : "llvm.llc+");

  llvm::Triple triple(mod->getTargetTriple());
  if (triple.getTriple().empty()) {
    triple.setTriple(HOST_TRIPLE);
  }
  configureTargetDependentOptions(triple, filetype);

  const Target* target = NULL;
  string err;
  target = llvm::TargetRegistry::lookupTarget(triple.getTriple(), err);
  if (!target) {
    llvm::errs() << "Error: unable to pick a target for compiling to assembly"
              << "\n";
    exit(1);
  }

  CodeGenOpt::Level
         cgOptLevel = optOptimizeZero
                        ? CodeGenOpt::None
                        : CodeGenOpt::Aggressive;

  CodeModel::Model cgModel = CodeModel::Default;
  TargetMachine* tm = target->createTargetMachine(triple.getTriple(),
                                                 "", // CPU
                                                 "", // Features
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

  tm->setMCUseCFI(optCFI != "no");
  tm->setAsmVerbosityDefault(true);
  // TODO don't use .loc directives for OS X 10.5 and prior.

  PassManager passes;
  // Use specific target data if available, else generic target data.
  if (const TargetData* td = tm->getTargetData()) {
    passes.add(new TargetData(*td));
  } else {
    passes.add(new TargetData(mod));
  }

  llvm::raw_fd_ostream raw_out(filename.c_str(), err,
                               fdFlagsForObjectType(filetype));
  ASSERT(err.empty()) << "Error when opening file to print output to:\n\t"
                      << err;

  llvm::formatted_raw_ostream out(raw_out,
      llvm::formatted_raw_ostream::PRESERVE_STREAM);


  bool disableVerify = true;
  if (tm->addPassesToEmitFile(passes, out, filetype,
#ifndef LLVM_DEFAULT_TARGET_TRIPLE
                              cgOptLevel,
#endif
                              disableVerify)) {
    llvm::errs() << "Unable to emit assembly file! " << "\n";
    exit(1);
  }

  // TODO: LLVM 3.0 and earlier will crash in X86ISelDAG with CodeGenOpt::None
  // when using llvm.gcroot of bitcast values and FastISel.
  // http://llvm.org/bugs/show_bug.cgi?id=10799
  llvm::EnableFastISel = false;
  // We disable here (after adding passes) because adding passes causes LLVM
  // to reset the flag based on a command-line option that we can't access.

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

  llvm::sys::Path mainModulePath(optInputPath);
  makePathAbsolute(mainModulePath);

  llvm::Module* module = readLLVMModuleFromPath(mainModulePath.str());

  if (optCleanupOnly) {
    foster::runCleanupPasses(*module);
    dumpModuleToBitcode(module, (gOutputNameBase + ".cleaned.bc"));
    foster::runWarningPasses(*module);
  } else {
    optimizeModuleAndRunPasses(module);

    if (optDumpPostOptIR) {
      dumpModuleToFile(module,  (gOutputNameBase + ".postopt.ll"));
    }

    compileToNativeAssemblyOrObject(module, optOutputName);
  }

  if (optDumpStats) {
    string err;
    llvm::raw_fd_ostream out((gOutputNameBase + ".optc.stats.txt").c_str(), err);
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

