// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/Linker.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Config/config.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/System/Host.h"
#include "llvm/System/Signals.h"
#include "llvm/System/TimeValue.h"
#include "llvm/System/Program.h"

////////////////////////////////////////////////////////////////////

#include "base/Assert.h"
#include "base/LLVMUtils.h"
#include "base/TimingsRepository.h"

#include "passes/FosterPasses.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"
#include "parse/DumpStructure.h"
#include "parse/ProtobufUtils.h"
#include "parse/ParsingContext.h"

#include "passes/CodegenPass.h"
#include "passes/AddParentLinksPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ClosureConversionPass.h"
#include "_generated_/FosterAST.pb.h"

#include "parse/FosterSymbolTableTraits-inl.h"
#include "StandardPrelude.h"

#include <fstream>
#include <vector>

using namespace llvm;

using foster::ScopedTimer;
using foster::SourceRange;
using foster::EDiag;

namespace foster {
  struct ScopeInfo;
  extern bool gPrintLLVMImports; // in StandardPrelude.cpp
}

using std::string;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

// Given -o foo, fosterlower will write foo.preopt.bc
static cl::opt<string>
optOutputName("o",
  cl::desc("[foster] Base name of output file"),
  cl::init("out"));

static cl::opt<bool>
optCompileSeparately("c",
  cl::desc("[foster] Compile separately, don't automatically link imported modules"));

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
optDumpASTs("dump-asts",
  cl::desc("[foster] Dump intermediate ASTs (and ANLTR parse tree)"));

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

void dumpExprStructureToFile(ExprAST* ast, const string& filename) {
  ScopedTimer timer("io.file.dumpexpr");
  string errInfo;
  llvm::raw_fd_ostream out(filename.c_str(), errInfo);
  foster::dumpExprStructure(out, ast);
}

void linkTo(llvm::Module*& transient,
            const std::string& name,
            llvm::Module* module) {
  string errMsg;
  if (Linker::LinkModules(module, transient, &errMsg)) {
    llvm::errs() << "Error when linking in " << name << ": " << errMsg << "\n";
  }
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
  ModuleAST* exprAST = NULL;
  foster::fepb::SourceModule sm;
  llvm::GlobalVariable* current_coro = NULL;
  llvm::Function* coro_transfer = NULL;

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler backend\n");

  foster::gPrintLLVMImports = optPrintLLVMImports;
  foster::validateInputFile(optInputPath);

  foster::ensureDirectoryExists(dumpdirFile(""));

  foster::initializeLLVM();
  foster::ParsingContext::initCachedLLVMTypeNames();

  llvm::sys::Path mainModulePath(optInputPath);
  makePathAbsolute(mainModulePath);

  foster::ParsingContext::pushNewContext();

  llvm::Module* module = new Module(mainModulePath.str().c_str(), getGlobalContext());

  foster::validateInputFile("libfoster.bc");
  foster::validateInputFile("imath-wrapper.bc");

  libfoster_bc = readLLVMModuleFromPath("libfoster.bc");
  imath_bc = readLLVMModuleFromPath("imath-wrapper.bc");
  ASSERT(imath_bc) << "must have imath library!";

  const llvm::Type* mpz_struct_ty = imath_bc->getTypeByName("struct.mpz");
  if (!mpz_struct_ty) {
    EDiag() << "Unable to find imath bitcode library";
    program_status = 1; goto cleanup;
  }

  exprAST = readSourceModuleFromProtobuf(optInputPath, sm);
  if (!exprAST) {
    EDiag() << "Unable to parse module from protocol buffer!";
    program_status = 1; goto cleanup;
  }

  mp_int =
    llvm::PointerType::getUnqual(mpz_struct_ty);
  module->addTypeName("mp_int", mp_int);
  gTypeScope.insert("int", NamedTypeAST::get("int", mp_int));

  foster_generic_coro_t = libfoster_bc->getTypeByName("struct.foster_generic_coro");
  ASSERT(foster_generic_coro_t != NULL);
  module->addTypeName("pfoster_coro",
    llvm::PointerType::getUnqual(foster_generic_coro_t));

  module->addTypeName("unit",
    llvm::StructType::get(getGlobalContext(), false));

  current_coro = libfoster_bc->getNamedGlobal("current_coro");
  module->getOrInsertGlobal("current_coro",
    current_coro->getType()->getContainedType(0));

  // coro_transfer isn't automatically added because it's
  // only a declaration, not a definition.
  coro_transfer = llvm::dyn_cast<llvm::Function>(
                  module->getOrInsertFunction("coro_transfer",
    llvm::dyn_cast<llvm::FunctionType>(
                    libfoster_bc->getFunction("coro_transfer")
                                ->getType()->getContainedType(0))));
  coro_transfer->addAttribute(1, llvm::Attribute::InReg);
  coro_transfer->addAttribute(2, llvm::Attribute::InReg);

  // TODO mark foster__assert as alwaysinline

  foster::putModuleMembersInScope(libfoster_bc, module);
  foster::putModuleMembersInInternalScope("imath", imath_bc, module);
  foster::addConcretePrimitiveFunctionsTo(module);

  if (!exprAST) {
    EDiag() << "Unable to parse module from protocol buffer!";
    program_status = 1; goto cleanup;
  }

  foster::addParentLinks(exprAST);

  if (optDumpASTs) { ScopedTimer timer("io.file");
    string outfile = "pp-precc.txt";
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Pretty printing to " << outfile << "\n";
    std::ofstream out(dumpdirFile(outfile).c_str());
    llvm::raw_os_ostream rout(out);

    ScopedTimer pptimer("io.prettyprint");
    foster::prettyPrintExpr(exprAST, rout);
  }

  if (optCompileSeparately) {
    // Need to emit before closure conversion, which alters
    // the set of top-level function definitions, but not
    // in a way that's relevant to importing modules.
    std::string outPbFilename(mainModulePath.getLast().str() + ".pb");
    dumpModuleToProtobuf(exprAST, dumpdirFile(outPbFilename));
  }

  {
    dumpExprStructureToFile(exprAST, dumpdirFile("structure.beforecc.txt"));

    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Performing closure conversion..." << "\n";

    foster::performClosureConversion(foster::globalNames, exprAST);

    dumpExprStructureToFile(exprAST, dumpdirFile("structure.aftercc.txt"));
  }

  if (optDumpASTs) {
    dumpModuleToProtobuf(exprAST, dumpdirFile("ast.postcc.pb"));

    ScopedTimer timer("io.file");
    string outfile = "pp-postcc.txt";
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Pretty printing to " << outfile << "\n";
    std::ofstream out(dumpdirFile(outfile).c_str());
    ScopedTimer pptimer("io.prettyprint");

    llvm::raw_os_ostream rout(out);
    foster::prettyPrintExpr(exprAST, rout);
  }

  llvm::outs() << "=========================" << "\n";

  {
    foster::codegen(exprAST, module);

    // Run cleanup passes on newly-generated code,
    // rather than wastefully on post-linked code.
    foster::runCleanupPasses(*module);
  }

  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module, dumpdirFile(optOutputName + ".prelink.ll").c_str());
  }

  { ScopedTimer timer("llvm.link");
    linkTo(libfoster_bc, "libfoster.bc", module);
    linkTo(imath_bc, "imath.bc", module);
  }

  if (optDumpPostLinkedIR) {
    dumpModuleToFile(module, dumpdirFile(optOutputName + ".preopt.ll"));
  }

  dumpModuleToFile(module, dumpdirFile(optOutputName + ".preopt.bc"));

  if (optDumpStats) {
    string err;
    llvm::raw_fd_ostream out(dumpdirFile(optOutputName + "lower.stats.txt").c_str(), err);
    llvm::PrintStatistics(out);
  }

  google::protobuf::ShutdownProtobufLibrary();
  foster::gInputFile = NULL;
  {
    llvm::outs().flush();
    llvm::errs().flush();
  }

cleanup:
  foster::ParsingContext::popCurrentContext();

  delete wholeProgramTimer;

  delete libfoster_bc; libfoster_bc = NULL;
  delete imath_bc; imath_bc = NULL;
  delete module; module = NULL;

  if (optPrintTimings) {
    setTimingDescriptions();
    foster::gTimings.print();
  }
  return program_status;
}

