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
#include "parse/DumpStructure.h"
#include "parse/ProtobufToAST.h"
#include "parse/ParsingContext.h"
#include "parse/CompilationContext.h"

#include "passes/TypecheckPass.h"
#include "passes/CodegenPass.h"
#include "passes/AddParentLinksPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ClosureConversionPass.h"
#include "passes/DumpToProtobuf.h"

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

void dumpModuleToProtobuf(ModuleAST* mod, const string& filename) {
  foster::pb::Expr pbModuleExpr;

  { ScopedTimer timer("protobuf");
    DumpToProtobufPass p(&pbModuleExpr); mod->accept(&p);
  }

  { ScopedTimer timer("protobuf.io");
    std::ofstream out(filename.c_str(),
                      std::ios::trunc | std::ios::binary);
    pbModuleExpr.SerializeToOstream(&out);

    std::ofstream txtout((filename + ".txt").c_str(), std::ios::trunc);
    txtout << pbModuleExpr.DebugString();
  }
}

ExprAST* readExprFromProtobuf(const string& pathstr) {
  foster::pb::Expr pbe;
  std::fstream input(pathstr.c_str(), std::ios::in | std::ios::binary);
  if (!pbe.ParseFromIstream(&input)) {
    return NULL;
  }

  return foster::ExprAST_from_pb(&pbe);
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

ModuleAST* parseModuleFromSourceFile(
              const llvm::sys::Path& sourceFilePath,
              int& err_status) {
  err_status = 0;

  std::string tmpProtobufFile("_tmpast.foster.pb");

  std::vector<const char*> nullTerminatedArgs;
  nullTerminatedArgs.push_back("fosterparse");
  nullTerminatedArgs.push_back(optInputPath.c_str());
  nullTerminatedArgs.push_back(tmpProtobufFile.c_str());
  nullTerminatedArgs.push_back(NULL);

  const llvm::sys::Path* redirects[] = { NULL, NULL, NULL };

  llvm::sys::Path path_to_fosterparse(
            llvm::sys::Program::FindProgramByName("fosterparse"));

  if (path_to_fosterparse.str().empty()) {
    path_to_fosterparse = "fosterparse";
  }

  if (path_to_fosterparse.exists() &&
      path_to_fosterparse.canRead() &&
      path_to_fosterparse.canExecute()) {
    // great!
  } else {
    foster::EDiag() << "unable to find or execute "
                    << path_to_fosterparse.str();
    err_status = 1;
    return NULL;
  }

  int parse_status = 0;
  int max_seconds_to_wait = 2;
  { ScopedTimer timer("io.parse");
    parse_status = llvm::sys::Program::ExecuteAndWait(
        path_to_fosterparse,
        &nullTerminatedArgs[0],
        0, // env
        &redirects[0],
        max_seconds_to_wait);
  }

  if (parse_status != 0) {
    llvm::errs() << llvm::sys::Program::FindProgramByName("fosterparse").str() << "\n";
    llvm::errs() << "Error (" << parse_status << ") invoking";
    for (int i = 0; i < nullTerminatedArgs.size(); ++i) {
      llvm::errs() << " " << nullTerminatedArgs[i];
    }
    llvm::errs() << " :: " << parse_status << "\n";
    llvm::errs().flush();
    llvm::outs() << "\n";
    llvm::outs().flush();
    err_status = parse_status;
    return NULL;
  }

  ModuleAST* exprAST = NULL;

  ExprAST* pbExprAST = readExprFromProtobuf(tmpProtobufFile);
  if (!pbExprAST) {
    foster::EDiag() << "unable to parse module from protobuf";
    err_status = 1;
    return NULL;
  }

  exprAST = dynamic_cast<ModuleAST*>(pbExprAST);
  if (!exprAST) {
    foster::EDiag() << "expression parsed from protobuf was not a ModuleAST";
    err_status = 1;
    return NULL;
  }

  // for each fn in module
  for (ModuleAST::FnAST_iterator it = exprAST->fn_begin();
                                it != exprAST->fn_end();
                                ++it) {
     gScope.getRootScope()->insert((*it)->getName(),
                                  (*it)->getProto());
  }

  return exprAST;
}

int main(int argc, char** argv) {
  int program_status = 0;
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  foster::linkFosterGC(); // statically, not dynamically
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;
  bool typechecked = false;
  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");
  Module* libfoster_bc = NULL;
  Module* imath_bc = NULL;
  const llvm::Type* mp_int = NULL;

  setDefaultCommandLineOptions();

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler\n");

  validateInputFile(optInputPath);

  ensureDirectoryExists(dumpdirFile(""));

  foster::initializeLLVM();

  llvm::sys::Path mainModulePath(optInputPath);
  mainModulePath.makeAbsolute();

  foster::ParsingContext::pushNewContext();

  ModuleAST* exprAST =
      parseModuleFromSourceFile(mainModulePath, program_status);

  if (!exprAST) {
    if (program_status == 0) { program_status = 2; }
    goto cleanup;
  }

  using foster::module;
  module = new Module(mainModulePath.str().c_str(), getGlobalContext());

  libfoster_bc = readLLVMModuleFromPath("libfoster.bc");
  imath_bc = readLLVMModuleFromPath("imath-wrapper.bc");
  mp_int =
    llvm::PointerType::getUnqual(imath_bc->getTypeByName("struct.mpz"));
  module->addTypeName("mp_int", mp_int);
  gTypeScope.insert("int", NamedTypeAST::get("int", mp_int));

  foster::putModuleMembersInScope(libfoster_bc, module);
  foster::putModuleMembersInInternalScope("imath", imath_bc, module);
  foster::addConcretePrimitiveFunctionsTo(module);

  {
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Adding parent links..." << "\n";
    foster::addParentLinks(exprAST);
  }

  {
  llvm::outs() << "=========================" << "\n";
  llvm::outs() << "Type checking... " << "\n";
  ScopedTimer timer("foster.typecheck");
  typechecked = foster::typecheck(exprAST);
  }

  if (!typechecked) {
    program_status = 1;
    goto cleanup;
  }

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

    ScopedTimer timer("foster.closureconv");
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
    ScopedTimer timer("foster.codegen");
    // Implicitly outputs to foster::module, via foster::builder.
    foster::codegen(exprAST);

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

  if (!optCompileSeparately) {
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

  { ScopedTimer timer("protobuf.shutdown");
    google::protobuf::ShutdownProtobufLibrary();
  }

  foster::gInputFile = NULL;
  { ScopedTimer timer("io.file.flush");
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

