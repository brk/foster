// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterSymbolTable.h"
#include "parse/FosterAST.h"

namespace foster {

SymbolTable<llvm::Value> scope;
SymbolTable<TypeAST> typeScope;
SymbolTable<ExprAST> varScope;

} // namespace foster

