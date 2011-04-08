// Copyright (c) 2009-2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/LLVMContext.h"
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

#include "parse/FosterLL.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h" // for foster_generic_coro_t
#include "parse/ProtobufToLLExpr.h"
#include "parse/ParsingContext.h" // for LLVM type names

#include "_generated_/FosterIL.pb.h"

#include "StandardPrelude.h"

#include <fstream>
#include <vector>

using std::string;

using foster::ScopedTimer;
using foster::EDiag;
using foster::ParsingContext;

namespace foster {
  struct ScopeInfo;
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

static cl::opt<bool>
optEmitDebugInfo("g",
  cl::desc("[foster] Emit debug information in generated LLVM IR"));

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

string dumpdirFile(const string& filename) {
  static string dumpdir("fc-output/");
  return dumpdir + filename;
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
  if (Linker::LinkModules(module, transient, &errMsg)) {
    llvm::errs() << "Error when linking in " << name << ": " << errMsg << "\n";
  }
}

void addCoroTransferDeclaration(llvm::Module* dst,
                                llvm::Module* src) {
  // coro_transfer isn't automatically added
  // because it's only a declaration, not a definition.
  llvm::Function* coro_transfer =
    llvm::dyn_cast<llvm::Function>(
      dst->getOrInsertFunction("coro_transfer",
      llvm::dyn_cast<llvm::FunctionType>(
             src->getFunction("coro_transfer")
                                ->getType()->getContainedType(0))));

  coro_transfer->addAttribute(1, llvm::Attribute::InReg);
  coro_transfer->addAttribute(2, llvm::Attribute::InReg);
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

namespace foster {
void codegenLL(LLModule* package, llvm::Module* mod);
}

int main(int argc, char** argv) {
  int program_status = 0;
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;
  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");
  Module* libfoster_bc = NULL;
  Module* imath_bc = NULL;
  const llvm::Type* mp_int = NULL;
  foster::bepb::Module pbin;
  llvm::GlobalVariable* current_coro = NULL;

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler backend\n");

  foster::gPrintLLVMImports = optPrintLLVMImports;
  foster::validateInputFile(optInputPath + ".ll.pb");

  foster::ensureDirectoryExists(dumpdirFile(""));

  foster::initializeLLVM();
  foster::ParsingContext::initCachedLLVMTypeNames();

  llvm::sys::Path mainModulePath(optInputPath);
  makePathAbsolute(mainModulePath);

  foster::ParsingContext::pushNewContext();

  llvm::Module* module = new Module(mainModulePath.str().c_str(), getGlobalContext());

  libfoster_bc = readLLVMModuleFromPath("_bitcodelibs_/libfoster.bc");
  imath_bc     = readLLVMModuleFromPath("_bitcodelibs_/imath-wrapper.bc");
  ASSERT(imath_bc) << "must have imath library!";

  const llvm::Type* mpz_struct_ty = imath_bc->getTypeByName("struct.mpz");
  if (!mpz_struct_ty) {
    EDiag() << "Unable to find imath bitcode library";
    program_status = 1; goto cleanup;
  }

  mp_int =
    llvm::PointerType::getUnqual(mpz_struct_ty);
  module->addTypeName("mp_int", mp_int);
  ParsingContext::insertType("int", NamedTypeAST::get("int", mp_int));

  foster_generic_coro_t = libfoster_bc->getTypeByName("struct.foster_generic_coro");
  ASSERT(foster_generic_coro_t != NULL);
  module->addTypeName("pfoster_coro",
    llvm::PointerType::getUnqual(foster_generic_coro_t));

  module->addTypeName("unit",
    llvm::StructType::get(getGlobalContext(), false));

  current_coro = libfoster_bc->getNamedGlobal("current_coro");
  module->getOrInsertGlobal("current_coro",
    current_coro->getType()->getContainedType(0));

  addCoroTransferDeclaration(module, libfoster_bc);
  // TODO mark foster__assert as alwaysinline

  foster::putModuleMembersInScope(libfoster_bc, module);
  foster::putModuleMembersInInternalScope("imath", imath_bc, module);
  foster::addConcretePrimitiveFunctionsTo(module);

  //================================================================
  //================================================================

  {
    LLModule* prog = readLLProgramFromProtobuf(optInputPath + ".ll.pb", pbin);
    ASSERT(prog) << "Unable to read LL program from protobuf!";

    foster::codegenLL(prog, module);

    // Run cleanup passes on newly-generated code,
    // rather than wastefully on post-linked code.
    foster::runCleanupPasses(*module);
  }


  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module, dumpdirFile(optOutputName + ".prelink.ll").c_str());
  }

  { ScopedTimer timer("llvm.link");
    linkTo(libfoster_bc, "libfoster", module);
    linkTo(imath_bc,     "imath",     module);
  }

  if (optDumpPostLinkedIR) {
    dumpModuleToFile(module, dumpdirFile(optOutputName + ".preopt.ll"));
  }

  dumpModuleToBitcode(module, dumpdirFile(optOutputName + ".preopt.bc"));

  if (optDumpStats) {
    string err;
    llvm::raw_fd_ostream out(dumpdirFile(optOutputName + "lower.stats.txt").c_str(), err);
    llvm::PrintStatistics(out);
  }

  google::protobuf::ShutdownProtobufLibrary();
  foster::gInputFile = NULL;
  llvm::outs().flush();
  llvm::errs().flush();

cleanup:
  foster::ParsingContext::popCurrentContext();

  delete wholeProgramTimer;

  delete libfoster_bc; libfoster_bc = NULL;
  delete imath_bc; imath_bc = NULL;
  delete module; module = NULL;

  if (optPrintTimings) {
    setTimingDescriptions();
    foster::gTimings.print("fosterlower");
  }
  return program_status;
}

