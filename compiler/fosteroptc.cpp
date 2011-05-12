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
#include "llvm/Config/config.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegistry.h"
#include "llvm/Target/TargetOptions.h"

#include "pystring/pystring.h"

#include "base/LLVMUtils.h"

#include "llvm/Support/Host.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/StandardPasses.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"

////////////////////////////////////////////////////////////////////

#include "base/Assert.h"
#include "base/TimingsRepository.h"

#include "passes/FosterPasses.h"

#include <fstream>
#include <vector>

using namespace llvm;

using foster::ScopedTimer;
using foster::SourceRange;
using foster::EDiag;

namespace foster {
  struct ScopeInfo;
  void linkFosterGC(); // defined in llmv/plugins/FosterGC.cpp
}

using std::string;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file.bc/ll>"));

static cl::opt<string>
optOutputName("o",
  cl::desc("[foster] Output file; with no extension, writes <out>.s"));

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

static cl::list<const PassInfo*, bool, PassNameParser>
cmdLinePassList(cl::desc("Optimizations available:"));

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
  gTimings.describe("llvm.llc+", "Time spent doing llc's job (IR->obj) (ms)");
}

Module* readLLVMModuleFromPath(string path) {
  foster::validateInputFile(path);
  ScopedTimer timer("io.file.readmodule");
  return foster::readLLVMModuleFromPath(path);
}

void dumpModuleToFile(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.ir");
  foster::dumpModuleToFile(mod, filename);
}

void dumpModuleToBitcode(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.bitcode");
  foster::dumpModuleToBitcode(mod, filename);
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

  foster::runFunctionPassesOverModule(fpasses, mod);
  passes.run(*mod);
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

  PassManager passes;
  if (const TargetData* td = tm->getTargetData()) {
    passes.add(new TargetData(*td));
  } else {
    passes.add(new TargetData(mod));
  }

  int flags = 0;
  if (filetype == TargetMachine::CGFT_ObjectFile) {
    flags |= raw_fd_ostream::F_Binary;
  }

  llvm::raw_fd_ostream raw_out(filename.c_str(), err, flags);
  ASSERT(err.empty()) << "Error when opening file to print output to:\n\t"
                      << err;

  llvm::formatted_raw_ostream out(raw_out,
      llvm::formatted_raw_ostream::PRESERVE_STREAM);

  // TODO: LLVM 2.9 and earlier sometimes crashes in X86ISelDAG
  // with CodeGenOpt::None; is that our fault or theirs?
  CodeGenOpt::Level
         cgOptLevel = optOptimizeZero
                        ? CodeGenOpt::Less // None, Default
                        : CodeGenOpt::Aggressive;

  bool disableVerify = true;
  if (tm->addPassesToEmitFile(passes, out,
      filetype, cgOptLevel, disableVerify)) {
    llvm::errs() << "Unable to emit assembly file! " << "\n";
    exit(1);
  }

  passes.run(*mod);
}

void setDefaultCommandLineOptions() {
  if (string(LLVM_HOSTTRIPLE).find("darwin") != string::npos) {
    // Applications on Mac OS X (x86) must be compiled with relocatable symbols,
    // which is -mdynamic-no-pic (GCC) or -relocation-model=dynamic-no-pic (llc).
    // Setting the flag here gives us the proper default, while still allowing
    // the user to override via command line options if need be.
    llvm::TargetMachine::setRelocationModel(llvm::Reloc::DynamicNoPIC);
  }

  // Ensure we always compile with -disable-fp-elim
  // to enable simple stack walking for the GC.
  llvm::NoFramePointerElim = true;
}

int main(int argc, char** argv) {
  int program_status = 0;
  foster::linkFosterGC(); // statically, not dynamically
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;
  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");

  setDefaultCommandLineOptions();

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler backend (LLVM optimization)\n");

  ASSERT(optOutputName != "");
  if ( pystring::endswith(optOutputName, ".o")
    || pystring::endswith(optOutputName, ".s")) {
    gOutputNameBase = string(optOutputName.begin(), optOutputName.end() - 2);
  } else if (pystring::endswith(optOutputName, ".obj")) {
    gOutputNameBase = string(optOutputName.begin(), optOutputName.end() - 4);
  } else {
    gOutputNameBase = optOutputName;
    optOutputName = optOutputName + ".s";
  }

  foster::initializeLLVM();

  llvm::sys::Path mainModulePath(optInputPath);
  makePathAbsolute(mainModulePath);

  llvm::Module* module = readLLVMModuleFromPath(mainModulePath.str());

  if (optCleanupOnly) {
    foster::runCleanupPasses(*module);
    dumpModuleToBitcode(module, (gOutputNameBase + ".cleaned.bc"));
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

