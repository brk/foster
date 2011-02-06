// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PROTOBUF_TO_AST_H
#define FOSTER_PROTOBUF_TO_AST_H

struct ExprAST;
struct TypeAST;
struct ModuleAST;

namespace foster {

namespace fepb {
  struct Expr;
  struct Type;
} // namespace foster::pb

//ModuleAST* ModuleAST_from_pb(pb::ExprAST);

ExprAST* ExprAST_from_pb(const fepb::Expr* e);

TypeAST* TypeAST_from_pb(const fepb::Type* t);

}

#endif
