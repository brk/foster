// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/System/Path.h"
#include "llvm/System/Process.h"

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "passes/DumpToProtobuf.h"
#include "parse/ProtobufUtils.h"
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

namespace foster {
void initCachedLLVMTypeNames();
} // namespace foster

int main(int argc, char** argv) {
  ///cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster parser\n");

  validateInputFile(optInputPath);
  validateOutputFile(optOutputPath);
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
