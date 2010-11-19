// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/System/Path.h"

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/InputTextBuffer.h"

#include "parse/FosterAST.h"
#include "parse/ProtobufToAST.h"
#include "parse/ProtobufUtils.h"

#include "passes/DumpToProtobuf.h"

#include <fstream>

using foster::EDiag;

ModuleAST* readSourceModuleFromProtobuf(const string& pathstr,
                                        foster::pb::SourceModule& out_sm) {
  std::fstream input(pathstr.c_str(), std::ios::in | std::ios::binary);
  if (!out_sm.ParseFromIstream(&input)) {
    return NULL;
  }

  ExprAST* expr = foster::ExprAST_from_pb(out_sm.mutable_expr());
  if (!expr) {
    EDiag() << "unable to parse expression from source module protobuf";
    return NULL;
  }

  return dynamic_cast<ModuleAST*>(expr);
}

void dumpModuleToProtobuf(ModuleAST* mod, const string& filename) {
  ASSERT(mod != NULL);

  foster::pb::SourceModule sm;
  const foster::InputTextBuffer* buf = mod->sourceRange.buf;
  if (buf) {
    for (int i = 0; i < buf->getLineCount(); ++i) {
      sm.add_line(buf->getLine(i));
    }
  }

  foster::pb::Expr* pbModuleExpr = sm.mutable_expr();
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

void validateInputFile(const string& pathstr) {
  llvm::sys::PathWithStatus path(pathstr);

  if (path.empty()) {
    EDiag() << "Error: need an input filename!";
    exit(1);
  }

  string err;
  const llvm::sys::FileStatus* status
         = path.getFileStatus(/*forceUpdate=*/ false, &err);
  if (!status) {
    if (err.empty()) {
      EDiag() << "Error occurred when reading input path '"
              << pathstr << "'";
    } else {
      EDiag() << "Error validating input path: " << err;
    }
    exit(1);
  }

  if (status->isDir) {
    EDiag() << "Error: input must be a file, not a directory!";
    exit(1);
  }
}

void validateOutputFile(const string& pathstr) {
  llvm::sys::Path outputPath(pathstr);
  llvm::sys::PathWithStatus path(outputPath.getDirname());

  if (pathstr.empty()) {
    EDiag() << "Error: need an output filename!";
    exit(1);
  }

  string err;
  const llvm::sys::FileStatus* status
         = path.getFileStatus(/*forceUpdate=*/ false, &err);
  if (!status) {
    if (err.empty()) {
      EDiag() << "Error occurred when reading output path '"
              << pathstr << "'";
    } else {
      EDiag() << "Error validating output path: " << err;
    }
    exit(1);
  }

  if (!status->isDir) {
    EDiag() << "Error: output directory must exist!";
    exit(1);
  }
}

