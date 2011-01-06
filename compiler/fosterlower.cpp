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
#include "llvm/Assembly/AssemblyAnnotationWriter.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Config/config.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegistry.h"
#include "llvm/Target/TargetOptions.h"

#include "llvm/Support/StandardPasses.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/Support/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/System/Host.h"
#include "llvm/System/Signals.h"
#include "llvm/System/TimeValue.h"
#include "llvm/System/Program.h"

////////////////////////////////////////////////////////////////////

#include "base/Assert.h"
#include "base/TimingsRepository.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterUtils.h"
#include "parse/DumpStructure.h"
#include "parse/ProtobufUtils.h"
#include "parse/ParsingContext.h"
#include "parse/CompilationContext.h"

#include "passes/CodegenPass.h"
#include "passes/AddParentLinksPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ClosureConversionPass.h"
#include "_generated_/FosterAST.pb.h"

#include "parse/FosterSymbolTableTraits-inl.h"
#include "StandardPrelude.h"

#include <memory>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>

using namespace llvm;

using foster::SourceRange;
using foster::EDiag;

namespace foster {
  struct ScopeInfo;
  void linkFosterGC(); // defined in llmv/plugins/FosterGC.cpp
  // Defined in foster/compiler/llvm/passes/ImathImprover.cpp
  llvm::Pass* createImathImproverPass();
  llvm::Pass* createGCMallocFinderPass();
}

using std::string;

#define FOSTER_VERSION_STR "0.0.5"
extern const char* ANTLR_VERSION_STR;

foster::TimingsRepository gTimings;

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


static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

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
optDumpPostOptIR("dump-postopt",
  cl::desc("[foster] Dump LLVM IR after linking and optimization passes"));

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
optOptimizeZero("O0",
  cl::desc("[foster] Disable optimization passes after linking with standard library"));

static cl::opt<bool>
optMake("make",
  cl::desc("[foster] Link and assemble"),
  cl::init(true));

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
}

void ensureDirectoryExists(const string& pathstr) {
  llvm::sys::Path p(pathstr);
  if (!p.isDirectory()) {
    p.createDirectoryOnDisk(true, NULL);
  }
}

Module* readLLVMModuleFromPath(string path) {
  ScopedTimer timer("io.file.readmodule");
  SMDiagnostic diag;
  return llvm::ParseIRFile(path, diag, llvm::getGlobalContext());
}

string dumpdirFile(const string& filename) {
  static string dumpdir("fc-output/");
  return dumpdir + filename;
}

struct CommentWriter : public AssemblyAnnotationWriter {
  void printInfoComment(const Value& v, formatted_raw_ostream& os) {
    if (v.getType()->isVoidTy()) return;
    os.PadToColumn(62);
    os << "; #uses = " << v.getNumUses() << "\t; " << str(v.getType()) ;
  }
};

void dumpModuleToFile(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.ir");
  string errInfo;
  llvm::raw_fd_ostream LLpreASM(filename.c_str(), errInfo);
  if (errInfo.empty()) {
    CommentWriter cw;
    mod->print(LLpreASM, &cw);
  } else {
    foster::EDiag() << "Error dumping module to " << filename << "\n"
                    << errInfo << "\n";
    exit(1);
  }
}

void dumpModuleToBitcode(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.bitcode");
  string errInfo;
  sys::RemoveFileOnSignal(sys::Path(filename), &errInfo);

  raw_fd_ostream out(filename.c_str(), errInfo, raw_fd_ostream::F_Binary);
  if (!errInfo.empty()) {
    foster::EDiag() << "Error when preparing to write bitcode to " << filename
        << "\n" << errInfo;
    exit(1);
  }

  WriteBitcodeToFile(mod, out);
}

void dumpExprStructureToFile(ExprAST* ast, const string& filename) {
  ScopedTimer timer("io.file.dumpexpr");
  string errInfo;
  llvm::raw_fd_ostream out(filename.c_str(), errInfo);
  foster::dumpExprStructure(out, ast);
}


TargetData* getTargetDataForModule(Module* mod) {
  const string& layout = mod->getDataLayout();
  if (layout.empty()) return NULL;
  return new TargetData(layout);
}

void runFunctionPassesOverModule(FunctionPassManager& fpasses, Module* mod) {
  fpasses.doInitialization();
  for (Module::iterator it = mod->begin(); it != mod->end(); ++it) {
    fpasses.run(*it);
  }
  fpasses.doFinalization();
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

  runFunctionPassesOverModule(fpasses, mod);
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

  PassManager passes;
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

  passes.run(*mod);
}

void linkTo(llvm::Module*& transient,
            const std::string& name,
            llvm::Module* module) {
  string errMsg;
  if (Linker::LinkModules(module, transient, &errMsg)) {
    llvm::errs() << "Error when linking in " << name << ": " << errMsg << "\n";
  }
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
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  foster::linkFosterGC(); // statically, not dynamically
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;
  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");
  Module* libfoster_bc = NULL;
  Module* imath_bc = NULL;
  const llvm::Type* mp_int = NULL;
  ModuleAST* exprAST = NULL;
  foster::pb::SourceModule sm;
  llvm::GlobalVariable* current_coro = NULL;
  llvm::Function* coro_transfer = NULL;

  setDefaultCommandLineOptions();

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler backend\n");

  validateInputFile(optInputPath);

  ensureDirectoryExists(dumpdirFile(""));

  foster::initializeLLVM();

  llvm::sys::Path mainModulePath(optInputPath);
  mainModulePath.makeAbsolute();

  foster::ParsingContext::pushNewContext();

  llvm::Module* module = new Module(mainModulePath.str().c_str(), getGlobalContext());

  validateInputFile("libfoster.bc");
  validateInputFile("imath-wrapper.bc");

  libfoster_bc = readLLVMModuleFromPath("libfoster.bc");
  imath_bc = readLLVMModuleFromPath("imath-wrapper.bc");
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
    llvm::FunctionPassManager fpasses(module);
    fpasses.add(foster::createImathImproverPass());
    runFunctionPassesOverModule(fpasses, module);

    PassManager passes;
    passes.add(foster::createGCMallocFinderPass());
    passes.run(*module);
  }

  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module, dumpdirFile("out.prelink.ll").c_str());
  }

  if (optMake) {
    { ScopedTimer timer("llvm.link");
      linkTo(libfoster_bc, "libfoster.bc", module);
      linkTo(imath_bc, "imath.bc", module);
    }

    if (optDumpPostLinkedIR) {
      dumpModuleToFile(module, dumpdirFile("out.preopt.ll"));
    }

    optimizeModuleAndRunPasses(module);

    if (optDumpPostOptIR) {
      dumpModuleToFile(module, dumpdirFile("out.postopt.ll"));
    }

    compileToNativeAssembly(module, dumpdirFile("out.s"));
  } else { // -c, compile to module instead of native assembly
    std::string outBcFilename(mainModulePath.getLast().str() + ".out.bc");
    dumpModuleToBitcode(module, dumpdirFile(outBcFilename));
  }
  // TODO invoke g++ .s -> exe

  if (optDumpStats) {
    string err;
    llvm::raw_fd_ostream out(dumpdirFile("stats.txt").c_str(), err);
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
    gTimings.print();
  }
  return program_status;
}

