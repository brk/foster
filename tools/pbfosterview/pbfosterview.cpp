// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/DerivedTypes.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/raw_ostream.h"

// These macros are conflicted between llvm/Config/config.h and antlr3config.h
#undef PACKAGE_BUGREPORT
#undef PACKAGE_NAME
#undef PACKAGE_STRING
#undef PACKAGE_TARNAME
#undef PACKAGE_VERSION

#include "base/Assert.h"
#include "base/InputFile.h"
#include "base/PathManager.h"

#include "parse/FosterAST.h"
#include "parse/ParsingContext.h"
#include "parse/CompilationContext.h"
#include "parse/ProtobufToAST.h"
#include "parse/ProtobufUtils.h"
#include "parse/DumpStructure.h"

#include "passes/PrettyPrintPass.h"
#include "_generated_/FosterAST.pb.h"

#include "pystring/pystring.h"

#include <memory>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>

using namespace llvm;

using foster::SourceRange;
using foster::EDiag;

using std::string;



static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<bool>
optSignaturesOnly("sigs-only", cl::desc("Print signatures only"));

static cl::opt<bool>
optTreeView("treeview", cl::desc("Print AST in tree format"));

static cl::opt<bool>
optRawAST("rawast", cl::desc("View raw AST dump"));

////////////////////////////////////////////////////////////////////

int main(int argc, char** argv) {
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  cl::ParseCommandLineOptions(argc, argv, "Foster Protobuf Viewer\n");

  foster::initializeLLVM();

  validateInputFile(optInputPath);

  foster::pb::SourceModule sm;
  ModuleAST* mod = readSourceModuleFromProtobuf(optInputPath, sm);
  if (!mod) {
    foster::EDiag() << "expression parsed from protobuf was not a ModuleAST";
    exit(1);
  }

  if (optRawAST) {
    llvm::outs() << mod->scope->getName() << "\n";
    for (size_t i = 0; i < mod->parts.size(); ++i) {
      llvm::outs() << str(mod->parts[i]) << "\n";
    }
  } else if (optTreeView) {
    foster::dumpExprStructure(llvm::outs(), mod);
  } else {
    foster::prettyPrintExpr(mod, llvm::outs(), 80, 2,
                            optSignaturesOnly);
  }

  return 0;
}

