// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Support/CommandLine.h"
#include "llvm/System/Path.h"

#include "base/InputFile.h"
#include "base/LLVMUtils.h"
#include "base/InputTextBuffer.h"
#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"

#include "passes/DumpToProtobuf.h"

#include <fstream>
#include <string>

// Usage:
//        fosterparse <inputfile.foster> <outputfile.pb>
// Input: a path to a Foster source file.
// Output: an AST corresponding to the input source,
//         serialized in Protobuf format.

using namespace llvm;
using std::string;
using foster::EDiag;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<string>
optOutputPath(cl::Positional, cl::desc("<output file>"));

void dumpModuleToProtobuf(ModuleAST* mod, const string& filename) {
  ASSERT(mod != NULL);

  foster::fepb::SourceModule sm;
  const foster::InputTextBuffer* buf = mod->sourceRange.buf;
  if (buf) {
    for (int i = 0; i < buf->getLineCount(); ++i) {
      sm.add_line(buf->getLine(i));
    }
  }

  foster::fepb::Expr* pbModuleExpr = sm.mutable_expr();
  DumpToProtobufPass p(pbModuleExpr); mod->accept(&p);

  if (!pbModuleExpr->IsInitialized()) {
    EDiag() << "Protobuf message is not initialized!\n";
  }

  if (filename == "-") {
    EDiag() << "warning: dumping module to file named '-', not stdout!";
  }

  std::string debug_filename = filename + ".dbg.txt";
  std::ofstream debug_out(debug_filename.c_str(),
                          std::ios::trunc | std::ios::binary);
  debug_out << pbModuleExpr->DebugString();

  std::ofstream out(filename.c_str(),
                  std::ios::trunc | std::ios::binary);
  if (sm.SerializeToOstream(&out)) {
    // ok!
  } else {
    EDiag() << "serialization returned false\n";
  }
}

int main(int argc, char** argv) {
  ///cl::SetVersionPrinter(&printVersionInfo);
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster parser\n");

  foster::validateInputFile(optInputPath);
  foster::validateOutputFile(optOutputPath);
  llvm::sys::Path inPath(optInputPath);
  const foster::InputFile infile(inPath);

  pANTLR3_BASE_TREE parseTree = NULL;
  foster::ANTLRContext* ctx = NULL;
  unsigned numParseErrors = 0;

  foster::ParsingContext::initCachedLLVMTypeNames();

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
