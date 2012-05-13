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

static cl::opt<bool>
optEmitDebugInfo("g",
  cl::desc("[foster] Emit debug information in generated LLVM IR"));

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
  for (size_t i = 0; i < decls.size(); ++i) {
    LLDecl*   d = decls[i];
    TypeAST*  t = d->getType();
    Function* f = mod->getFunction(d->getName());
    Value* v;
    if (!f) { v = mod->getGlobalVariable(d->getName()); }
    else { // Make sure function callconv matches
      FnTypeAST* fnty = dynamic_cast<FnTypeAST*>(t);
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
  void codegenLL(LLModule*, llvm::Module* mod, bool useGC, bool nsw, bool nuw);
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
    coro_bc = readLLVMModuleFromPath("_bitcodelibs_/gc_bc/libfoster_coro.bc");
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

  libfoster_bc = readLLVMModuleFromPath("_bitcodelibs_/libfoster.bc");
  foster::putModuleFunctionsInScope(libfoster_bc, module);

  //imath_bc     = readLLVMModuleFromPath("_bitcodelibs_/imath-wrapper.bc");
  //ASSERT(imath_bc) << "must have imath library!";
  //llvm::Type* mpz_struct_ty = imath_bc->getTypeByName("struct.mpz");
  //if (!mpz_struct_ty) {
  //  EDiag() << "Unable to find imath bitcode library";
  //  program_status = 1; goto cleanup;
  //}
  //mp_int = llvm::PointerType::getUnqual(mpz_struct_ty);
  //module->addTypeName("mp_int", mp_int);
  //foster::ParsingContext::insertType("Int",
  //             PrimitiveTypeAST::get("Int", mp_int));
  //foster::putModuleMembersInScope(imath_bc, module);

  //================================================================
  //================================================================

  {
    LLModule* prog = readLLProgramFromProtobuf(optInputPath, pbin);
    ASSERT(prog) << "Unable to read LL program from protobuf!";

    if(!areDeclaredValueTypesOK(module, prog->val_decls)) {
      program_status = 1; goto cleanup;
    }

    foster::codegenLL(prog, module, !optDisableGC, optForceNSW, optForceNUW);
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

