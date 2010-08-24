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
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Config/config.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetRegistry.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Target/SubtargetFeature.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Support/StandardPasses.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/IRReader.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/System/Host.h"
#include "llvm/System/Signals.h"
#include "llvm/System/TimeValue.h"

// These macros are conflicted between llvm/Config/config.h and antlr3config.h
#undef PACKAGE_BUGREPORT
#undef PACKAGE_NAME
#undef PACKAGE_STRING
#undef PACKAGE_TARNAME
#undef PACKAGE_VERSION

#include "base/Assert.h"
#include "base/InputFile.h"
#include "base/TimingsRepository.h"
#include "base/PathManager.h"

#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h"
#include "parse/CompilationContext.h"

#include "passes/BuildCFG.h"
#include "passes/TypecheckPass.h"
#include "passes/CodegenPass.h"
#include "passes/AddParentLinksPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ClosureConversionPass.h"
#include "passes/DumpToProtobuf.h"

#include "StandardPrelude.h"

#include <memory>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>

using namespace llvm;

using foster::LLVMTypeFor;
using foster::SourceRange;
using foster::EDiag;

namespace foster {
  struct ScopeInfo;
  void linkFosterGC(); // defined in llmv/plugins/FosterGC.cpp
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

static cl::list<std::string>
optIncludeRoots("I",
  cl::desc("Seach directories for imported modules"),
  cl::Prefix,
  cl::ZeroOrMore);

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

#ifdef LLVM_GE_2_8
static cl::opt<bool>
optDumpStats("dump-stats",
  cl::desc("[foster] Dump timing and other statistics from compilation"));
#endif

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

string dotdirFile(const string& filename) {
  return dumpdirFile("dot/" + filename);
}

void dumpScopesToDotGraphs() {
  ScopedTimer timer("io.dot");
  {
    std::string err;
    llvm::raw_fd_ostream f(dumpdirFile("gScope.dot").c_str(), err);
    if (err.empty()) {
      llvm::WriteGraph(f, &gScope);
    } else {
      foster::EDiag() << "no file to write gScope.dot";
    }
  }

  {
    std::string err;
    llvm::raw_fd_ostream f(dumpdirFile("gTypeScope.dot").c_str(), err);
    if (err.empty()) {
      llvm::WriteGraph(f, &gTypeScope);
    } else {
      foster::EDiag() << "no file to write gTypeScope.dot";
    }
  }
}

void dumpModuleToFile(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.ir");
  string errInfo;
  llvm::raw_fd_ostream LLpreASM(filename.c_str(), errInfo);
  if (errInfo.empty()) {
    LLpreASM << *mod;
  } else {
    llvm::errs() << "Error dumping module to " << filename << "\n";
    llvm::errs() << errInfo << "\n";
    exit(1);
  }
}

void dumpModuleToBitcode(Module* mod, const string& filename) {
  ScopedTimer timer("io.file.dumpmodule.bitcode");
  string errInfo;
  sys::RemoveFileOnSignal(sys::Path(filename), &errInfo);

  raw_fd_ostream out(filename.c_str(), errInfo, raw_fd_ostream::F_Binary);
  if (!errInfo.empty()) {
    llvm::errs() << "Error when preparing to write bitcode to " << filename
        << "\n" << errInfo << "\n";
    exit(1);
  }

  WriteBitcodeToFile(mod, out);
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
  }
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

  fpasses.doInitialization();
  for (Module::iterator it = mod->begin(); it != mod->end(); ++it) {
    fpasses.run(*it);
  }
  fpasses.doFinalization();

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

  // TODO replace TargetData from ee (in Codegen) with this TargetData
  FunctionPassManager passes(mod);
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

  passes.doInitialization();
  for (Module::iterator it = mod->begin(); it != mod->end(); ++it) {
    if (it->isDeclaration()) continue;
    passes.run(*it);
  }
  passes.doFinalization();
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

// Validates and registers all the -I<path> flags from the command line.
void collectIncludeRoots() {
  typedef cl::list<std::string>::iterator IncRootsIter;
  for (IncRootsIter it = optIncludeRoots.begin();
                   it != optIncludeRoots.end(); ++it) {
    llvm::sys::Path path(*it);
    if (path.isValid() && path.isDirectory()) {
      foster::gPathManager.registerModuleSearchPath(path);
    } else {
      llvm::sys::Path abspath(*it);
      abspath.makeAbsolute();
      std::cerr << "warning: ignoring input path \"" << path.str() << "\""
          << " because directory '" << abspath.str() << "' does not exist.\n";
    }
  }
}

void setDefaultCommandLineOptions() {
  if (string(LLVM_HOSTTRIPLE).find("darwin") != string::npos) {
    // Applications on Mac OS X must be compiled with relocatable symbols, which
    // is -mdynamic-no-pic (GCC) or -relocation-model=dynamic-no-pic (llc).
    // Setting the flag here gives us the proper default, while still allowing
    // the user to override via command line options if need be.
    llvm::TargetMachine::setRelocationModel(llvm::Reloc::DynamicNoPIC);
  }

  // Ensure we always compile with -disable-fp-elim
  // to enable simple stack walking for the GC.
  llvm::NoFramePointerElim = true;
}

int main(int argc, char** argv) {
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  foster::linkFosterGC(); // statically, not dynamically
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;

  ScopedTimer* wholeProgramTimer = new ScopedTimer("total");

  setDefaultCommandLineOptions();

  cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster compiler\n");

  collectIncludeRoots();
  validateInputFile(optInputPath);

  ensureDirectoryExists(dumpdirFile(""));
  ensureDirectoryExists( dotdirFile(""));

  using foster::module;
  using foster::ee;

  foster::initializeLLVM();

  llvm::sys::Path mainModulePath(optInputPath);
  mainModulePath.makeAbsolute();
  module = new Module(mainModulePath.str().c_str(), getGlobalContext());
  ee = EngineBuilder(module).create();
  initMaps();

  Module* m = readLLVMModuleFromPath("libfoster.bc");
  foster::putModuleMembersInScope(m, module);
  foster::createLLVMBitIntrinsics();
  
  llvm::sys::Path inPath(optInputPath);
  const foster::InputFile infile(inPath);
  foster::gInputFile = &infile;

  pANTLR3_BASE_TREE parseTree = NULL;
  foster::ANTLRContext* ctx = NULL;
  unsigned numParseErrors = 0;
  ModuleAST* exprAST = NULL;

  foster::CompilationContext cc;

  { ScopedTimer timer("io.parse");
    exprAST = foster::parseModule(infile, parseTree, ctx, numParseErrors, &cc);
  }
  
  foster::gCompilationContexts.push(&cc);

  if (optDumpASTs) {
    llvm::outs() << "dumping parse trees" << "\n";
    if (1) {
      std::ofstream out(dumpdirFile("stringtree.dump.txt").c_str());
      out << stringTreeFrom(parseTree) << "\n";
    }

    if (1) {
      dumpModuleToProtobuf(exprAST, dumpdirFile("ast.postparse.pb"));
    }
  }

  if (numParseErrors > 0) {
    exit(2);
  }

  {
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Adding parent links..." << "\n";
    foster::addParentLinks(exprAST);
  }
 
  {
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "building CFGs" << "\n";
    foster::buildCFG(exprAST);

    for (ModuleAST::FnAST_iterator it = exprAST->fn_begin();
           it != exprAST->fn_end(); ++it) {
      FnAST* fnast = *it;
      const string& name = fnast->proto->name;
      string filename(dotdirFile(name + ".dot"));
      if (!fnast->cfgs.empty()) {
        llvm::outs() << "Writing " << filename << "\n";
        std::string err;
        llvm::raw_fd_ostream f(filename.c_str(), err);
        if (err.empty()) { ScopedTimer timer("io.dot");
          llvm::WriteGraph(f, fnast);
        }
      } else {
        foster::EDiag() << "no CFG for " << name;
      }
    }
  }

  {
  llvm::outs() << "=========================" << "\n";
  llvm::outs() << "Type checking... " << "\n";
  }

  bool typechecked = false;
  { ScopedTimer timer("foster.typecheck");
    typechecked = typecheck(exprAST);
  }

  if (!typechecked) { return 1; }
  
  if (optDumpASTs) { ScopedTimer timer("io.file");
    string outfile = "pp-precc.txt";
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Pretty printing to " << outfile << "\n";
    std::ofstream out(dumpdirFile(outfile).c_str());
    ScopedTimer pptimer("io.prettyprint");
    foster::prettyPrintExpr(exprAST, llvm::outs());
  }

  if (optCompileSeparately) {
    // Need to emit before closure conversion, which alters
    // the set of top-level function definitions, but not
    // in a way that's relevant to importing modules.
    std::string outPbFilename(mainModulePath.getLast().str() + ".pb");
    dumpModuleToProtobuf(exprAST, dumpdirFile(outPbFilename));
  }

  {
    llvm::outs() << "=========================" << "\n";
    llvm::outs() << "Performing closure conversion..." << "\n";
  }

  { ScopedTimer timer("foster.closureconv");
    ClosureConversionPass p(foster::globalNames, exprAST);
    exprAST->accept(&p);
  }

  { ScopedTimer timer("io.file");
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
    CodegenPass cgPass; exprAST->accept(&cgPass);
  }
  
  if (optDumpPreLinkedIR) {
    dumpModuleToFile(module, dumpdirFile("out.prelink.ll").c_str());
  }

  dumpScopesToDotGraphs();

  if (!optCompileSeparately) {
    string errMsg;
    { ScopedTimer timer("llvm.link");
    if (Linker::LinkModules(module, m, &errMsg)) {
      llvm::errs() << "Error when linking modules: " << errMsg << "\n";
    }
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

#ifdef LLVM_GE_2_8
  if (optDumpStats) {
    string err;
    llvm::raw_fd_ostream out(dumpdirFile("stats.txt").c_str(), err);
    llvm::PrintStatistics(out);
  }
#endif

  { ScopedTimer timer("protobuf.shutdown");
    google::protobuf::ShutdownProtobufLibrary();
  }
  foster::gInputFile = NULL;
  { ScopedTimer timer("io.file.flush");
    llvm::outs().flush();
    llvm::errs().flush();
  }

  foster::gCompilationContexts.pop();
  foster::deleteANTLRContext(ctx);
  delete wholeProgramTimer;

  if (optPrintTimings) {
    setTimingDescriptions();
    gTimings.print();
  }
  return 0;
}

