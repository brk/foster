// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_DUMP_STRUCTURE
#define FOSTER_PASSES_DUMP_STRUCTURE

namespace llvm { class raw_ostream; }

class ExprAST;

namespace foster {
  void dumpExprStructure(llvm::raw_ostream& out, ExprAST* t);
} // namespace foster

#endif // header guard

