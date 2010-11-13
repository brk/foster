// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/System/Path.h"
#include "llvm/System/Process.h"

#include "base/InputFile.h"
#include "passes/DumpToProtobuf.h"
#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"

#include <string>
#include <iostream>
#include <fstream>

// Input: a path to a Foster source file.
// Output: an AST corresponding to the input source,
//         serialized in Protobuf format.

using namespace llvm;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<string>
optOutputPath(cl::Positional, cl::desc("<output file>"));

static cl::list<std::string>
optIncludeRoots("I",
  cl::desc("Seach directories for imported modules"),
  cl::Prefix,
  cl::ZeroOrMore);

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

void dueDiligenceForNotDumpingBinaryToStdout(const std::string& outpath) {
  if (outpath == "-" && sys::Process::StandardOutIsDisplayed()) {
    llvm::errs() << "Error: fosterparse's output is a binary file."
                 << " You probably want to redirect stdout to a file or something!"
                 << "\n";
    exit(2);
  }
}

void dumpModuleToProtobuf(ModuleAST* mod, const string& filename) {
  foster::pb::Expr pbModuleExpr;
  DumpToProtobufPass p(&pbModuleExpr); mod->accept(&p);

  std::ostream* out = NULL;
  if (filename == "-") {
    out = &std::cout;
  } else {
    out = new std::ofstream(filename.c_str(),
                            std::ios::trunc | std::ios::binary);
    std::string debug_filename = filename + ".dbg.txt";
    std::ofstream debug_out(debug_filename.c_str(),
                            std::ios::trunc | std::ios::binary);
    debug_out << pbModuleExpr.DebugString();
  }

  if (!pbModuleExpr.IsInitialized()) {
    llvm::errs() << "Protobuf message is not initialized!\n";
  }

  if (pbModuleExpr.SerializeToOstream(out)) {
    // ok!
  } else {
    llvm::outs() << "serialization returned false\n";
  }

  if (out != &std::cout) {
    delete out;
  } else {
    std::cout.flush();
  }
}

namespace foster {
void initCachedLLVMTypeNames();
} // namespace foster

int main(int argc, char** argv) {
  ///cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster parser\n");

  validateInputFile(optInputPath);
  dueDiligenceForNotDumpingBinaryToStdout(optOutputPath);

  llvm::sys::Path inPath(optInputPath);
  const foster::InputFile infile(inPath);

  pANTLR3_BASE_TREE parseTree = NULL;
  foster::ANTLRContext* ctx = NULL;
  unsigned numParseErrors = 0;

  foster::initCachedLLVMTypeNames();

  foster::ParsingContext::pushNewContext();
  ModuleAST* exprAST = foster::parseModule(infile, optInputPath,
                                parseTree, ctx, numParseErrors);
  if (numParseErrors > 0) {
    return 3;
  } else if (!exprAST) {
    return 4;
  }
  dumpModuleToProtobuf(exprAST, optOutputPath);
  return 0;
}
