// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/ADT/Statistic.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"

#include "base/LLVMUtils.h"
#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "base/TimingsRepository.h"

#include "parse/FosterAST.h"
#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"

#include <fstream>
#include <string>

#include "cbor.h"

// Usage:
//        fosterparse <inputfile.foster> <outputfile.pb>
// Input: a path to a Foster source file.
// Output: a concrete parse tree corresponding to the input source,
//         serialized in CBOR format.

using namespace llvm;
using std::string;

using foster::EDiag;
using foster::ScopedTimer;

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<string>
optOutputPath(cl::Positional, cl::desc("<output file>"));

static cl::list<string>
optIncludePath("I", cl::desc("Path to search for includes"),
                    cl::value_desc("include path"));

static cl::opt<bool>
optPrintTimings("fosterc-time",
  cl::desc("[foster] Print timing measurements of compiler passes"));

static cl::opt<bool>
optPrintCombined("fosterc-combined",
  cl::desc("[foster] Print combined source lines"));


void setTimingDescriptions() {
  using foster::gTimings;
  gTimings.describe("total", "Overall compiler runtime (ms)");

  gTimings.describe("io.parse", "Time spent parsing input file (ms)");
  gTimings.describe("io.cbor", "Time spent building + writing CBOR (ms)");
}

void dumpToCbor(cbor::encoder& e, InputWholeProgram* wp);

int main(int argc, char** argv) {
  cl::ParseCommandLineOptions(argc, argv, "Bootstrap Foster parser\n");

  foster::validateInputFile(optInputPath);
  foster::validateOutputFile(optOutputPath);
  const foster::InputFile infile(optInputPath);

  unsigned numParseErrors = 0;

  foster::ParsingContext::pushNewContext();

  InputWholeProgram* pgmAST = foster::parseWholeProgram(infile, optIncludePath, &numParseErrors);

  if (numParseErrors > 0) {
    EDiag() << "Encountered " << numParseErrors << " parsing errors; exiting."
            << (pgmAST ? " (with AST)" : " (without AST");
    return 3;
  } else if (!pgmAST) {
    return 4;
  }

  if (!optOutputPath.empty()) {
    ScopedTimer timer("io.cbor");
    cbor::output_dynamic output;
    cbor::encoder enc(output);
    dumpToCbor(enc, pgmAST);
    FILE* f = fopen(optOutputPath.c_str(), "w");
    fwrite((const void*) output.data(), 1, (size_t) output.size(), f);
    fclose(f);
  }

  if (optPrintCombined) {
    for (int i = 0; i < pgmAST->getModuleCount(); ++i) {
      auto m = pgmAST->getInputModule(i)->source;
      llvm::outs() << "// " << m->getPath() << "\n";
      llvm::outs() << m->getBuffer()->getMemoryBuffer()->getBuffer() << "\n";
    }
  }

  if (optPrintTimings) {
    setTimingDescriptions();
    foster::gTimings.print("fosterparse");
  }
  return 0;
}
