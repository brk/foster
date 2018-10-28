// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_PRETTYPRINT_PUGH
#define FOSTER_PASSES_PRETTYPRINT_PUGH

namespace llvm { class raw_ostream; }

class TypeAST;

namespace foster {
  void prettyPrintType(const TypeAST* t,
                 llvm::raw_ostream& out,
                 int width = 80, int indent_width = 2);

} // namespace foster

#endif // header guard

