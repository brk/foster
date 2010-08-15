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
#include "parse/CompilationContext.h"
#include "parse/ProtobufToAST.h"

#include "passes/PrettyPrintPass.h"

#include "_generated_/FosterAST.pb.h"

#include "pystring/pystring.h"

#include <memory>
#include <fstream>
#include <sstream>
#include <map>
#include <vector>

using namespace llvm;

using foster::LLVMTypeFor;
using foster::SourceRange;
using foster::EDiag;

using std::string;



static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

ExprAST* readExprFromProtobuf(const string& pathstr) {
  foster::pb::Expr pbe;
  std::fstream input(pathstr.c_str(), std::ios::in | std::ios::binary);
  if (!pbe.ParseFromIstream(&input)) {
    return NULL;
  }

  return foster::ExprAST_from_pb(&pbe);
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

int main(int argc, char** argv) {
  GOOGLE_PROTOBUF_VERIFY_VERSION;

  cl::ParseCommandLineOptions(argc, argv, "Foster Protobuf Viewer\n");

  foster::initializeLLVM();

  validateInputFile(optInputPath);

  ExprAST* exprAST = readExprFromProtobuf(optInputPath);
  if (!exprAST) {
    foster::EDiag() << "unable to parse module from protobuf";
    exit(1);
  }

  ModuleAST* mod = dynamic_cast<ModuleAST*>(exprAST);
  if (!mod) {
    foster::EDiag() << "expression parsed from protobuf was not a ModuleAST";
    exit(1);
  }

  PrettyPrintPass pp(std::cout, 80);
  mod->accept(&pp);

  return 0;
}

