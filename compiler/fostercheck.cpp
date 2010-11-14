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

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/DumpStructure.h"
#include "parse/ProtobufUtils.h"
#include "parse/ParsingContext.h"
#include "parse/CompilationContext.h"

#include "passes/TypecheckPass.h"
#include "passes/AddParentLinksPass.h"
#include "passes/PrettyPrintPass.h"
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


static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<string>
optOutputPath(cl::Positional, cl::desc("<output file>"));

void ensureDirectoryExists(const string& pathstr) {
  llvm::sys::Path p(pathstr);
  if (!p.isDirectory()) {
    p.createDirectoryOnDisk(true, NULL);
  }
}

Module* readLLVMModuleFromPath(string path) {
  SMDiagnostic diag;
  return llvm::ParseIRFile(path, diag, llvm::getGlobalContext());
}

string dumpdirFile(const string& filename) {
  static string dumpdir("fc-output/");
  return dumpdir + filename;
}

void dumpExprStructureToFile(ExprAST* ast, const string& filename) {
  string errInfo;
  llvm::raw_fd_ostream out(filename.c_str(), errInfo);
  foster::dumpExprStructure(out, ast);
}

int main(int argc, char** argv) {
  int program_status = 0;
  GOOGLE_PROTOBUF_VERIFY_VERSION;
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);
  llvm_shutdown_obj Y;
  bool typechecked = false;
  Module* libfoster_bc = NULL;
  Module* imath_bc = NULL;
  const llvm::Type* mp_int = NULL;

  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster type checker\n");
  validateInputFile(optInputPath);
  ensureDirectoryExists(dumpdirFile(""));
  foster::initializeLLVM();

  llvm::sys::Path mainModulePath(optInputPath);
  mainModulePath.makeAbsolute();

  if (optOutputPath == "") {
    optOutputPath = mainModulePath.str() + ".typechecked.pb";
  }

  foster::ParsingContext::pushNewContext();

  foster::pb::SourceModule sm;
  ModuleAST* exprAST = readSourceModuleFromProtobuf(mainModulePath.str(), sm);

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


  // for each fn in module
  for (ModuleAST::FnAST_iterator it = exprAST->fn_begin();
                                it != exprAST->fn_end();
                                ++it) {
     gScope.getRootScope()->insert((*it)->getName(),
                                  (*it)->getProto());
  }

  foster::addParentLinks(exprAST);


  typechecked = foster::typecheck(exprAST);
  if (!typechecked) {
    program_status = 1;
    goto cleanup;
  }

  dumpModuleToProtobuf(exprAST, optOutputPath);

cleanup:
  foster::ParsingContext::popCurrentContext();

  delete libfoster_bc; libfoster_bc = NULL;
  delete imath_bc; imath_bc = NULL;
  delete module; module = NULL;

  return program_status;
}

