// Copyright (c) 2010 Fen Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/LLVMUtils.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "passes/DumpToProtobuf.h"
#include "llvm/System/Path.h"

// Protobufs do not easily allow mirroring of existing object
// graph structures in the depth-first style preorder style usually
// associated with visitors, because repeated (pointer) fields only
// allow adding child nodes by requesting new nodes from the parent,
// and do not directly support adopting existing nodes as children.
//
// Thus, the way we'll transcribe our existing AST tree to protobufs
// is to store a "current parent pb::Expr*" as a pass field;
// each leaf will initialize the current node with its data,
// and interior nodes will reset the current pointer with newly-created
// pb::Expr*s before recursing to child nodes.

namespace pb = foster::fepb;

void dumpChild(DumpToProtobufPass* pass,
               pb::Expr* target,
               ExprAST* child) {
  ASSERT(child != NULL);
  pb::Expr* saved = pass->current;
  pass->current = target;
  child->dump(pass);
  pass->current = saved;
}

void dumpChildren(DumpToProtobufPass* pass,
                  ExprAST* ast) {
  pass->current->mutable_parts()->Reserve(ast->parts.size());
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    dumpChild(pass, pass->current->add_parts(), ast->parts[i]);
  }
}

void setSourceLocation(pb::SourceLocation* pbloc,
                       const foster::SourceLocation& loc) {
  pbloc->set_column(loc.column);
  pbloc->set_line(loc.line);
}

void setSourceRange(pb::SourceRange* pbr,
                    const foster::SourceRange& r) {
  if (r.source) {
    llvm::sys::Path p(r.source->getPath());
    makePathAbsolute(p); // TODO perhaps all paths should be stored absolute...?
    //pbr->set_file_path(p.str());
  }

  if (r.begin != foster::SourceLocation::getInvalidLocation()) {
    setSourceLocation(pbr->mutable_begin(), r.begin);
  }
  if (r.end   != foster::SourceLocation::getInvalidLocation()) {
    setSourceLocation(pbr->mutable_end(),   r.end);
  }
}

void processExprAST(pb::Expr* current,
                    ExprAST* ast,
                    pb::Expr::Tag tag) {
  current->set_tag(tag);

  if (ast->sourceRange.isValid()) {
    setSourceRange(current->mutable_range(), ast->sourceRange);
  }

  if (ast->type) {
    DumpTypeToProtobufPass dt(current->mutable_type());
    ast->type->dump(&dt);
  }
}

/////////////////////////////////////////////////////////////////////

void BoolAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::BOOL);
  pass->current->set_bool_value(this->boolValue);
}

void IntAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::PB_INT);
  pass->current->set_int_text(this->getOriginalText());
}

void VariableAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::VAR);
  pass->current->set_name(this->name);
}

void PrototypeAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::PROTO);
  pb::Proto* proto = pass->current->mutable_proto();
  proto->set_name(this->getName());

  proto->mutable_in_args()->Reserve(this->parts.size());
  for (size_t i = 0; i < this->inArgs.size(); ++i) {
    dumpChild(pass, proto->add_in_args(), this->inArgs[i]);
  }

  if (this->resultTy) {
    DumpTypeToProtobufPass dt(proto->mutable_result());
    this->resultTy->dump(&dt);
  }
}

void FnAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::FN);
  dumpChild(pass, pass->current->add_parts(), this->getProto());
  dumpChild(pass, pass->current->add_parts(), this->parts[0]);
}

void ModuleAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::MODULE);
  pass->current->set_name(this->name);
  dumpChildren(pass, this);
}

void IfExprAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::IF);
  pb::PBIf* if_ = pass->current->mutable_pb_if();
  dumpChild(pass, if_->mutable_test_expr(), this->getTestExpr());
  dumpChild(pass, if_->mutable_then_expr(), this->getThenExpr());
  dumpChild(pass, if_->mutable_else_expr(), this->getElseExpr());
}

void SubscriptAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::SUBSCRIPT);
  dumpChildren(pass, this);
}

void SeqAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::SEQ);
  dumpChildren(pass, this);
}

void CallAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::CALL);
  dumpChildren(pass, this);
}

void ETypeAppAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::TY_APP);
  dumpChildren(pass, this);
  DumpTypeToProtobufPass dt(pass->current->mutable_ty_app_arg_type());
  this->typeArg->dump(&dt);
}

void TupleExprAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::TUPLE);
  ASSERT(this->parts.size() == 1); // have a SeqAST wrapper...
  dumpChildren(pass, this->parts[0]);
}

void BuiltinCompilesExprAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::COMPILES);
  if (this->parts[0] == NULL) {
    this->parts.clear();
  }
  dumpChildren(pass, this);
}

/////////////////////////////////////////////////////////////////////

void dumpChild(DumpTypeToProtobufPass* pass,
               pb::Type* target,
               TypeAST* child) {
  if (!child) return;

  pb::Type* saved = pass->current;
  pass->current = target;
  child->dump(pass);
  pass->current = saved;
}

void setTagAndRange(pb::Type* target,
                    TypeAST* ast,
                    pb::Type::Tag tag) {
  target->set_tag(tag);
  if (ast->getSourceRange().isValid()) {
    setSourceRange(target->mutable_range(), ast->getSourceRange());
  }
}


void NamedTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::LLVM_NAMED);
  string tyname = str(this->getLLVMType());
  ASSERT(!tyname.empty());
  pass->current->set_name(tyname);
}

void TypeVariableAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::TYPE_VARIABLE);
  pass->current->set_name(this->getTypeVariableName());
}

void FnTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::FN);

  pb::FnType* fnty = pass->current->mutable_fnty();
  fnty->set_calling_convention(this->getCallingConventionName());

  if (this->getReturnType()) {
    dumpChild(pass, fnty->mutable_ret_type(), this->getReturnType());
  }

  fnty->mutable_arg_types()->Reserve(this->getNumParams());
  for (int i = 0; i < this->getNumParams(); ++i) {
    dumpChild(pass, fnty->add_arg_types(), this->getParamType(i));
  }

  fnty->set_is_closure(this->isMarkedAsClosure());
}

void RefTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::REF);

  if (this->getElementType()) {
    dumpChild(pass, pass->current->mutable_ref_underlying_type(), this->getElementType());
  }
}

void CoroTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::CORO);
  dumpChild(pass, pass->current->add_type_parts(), this->getContainedType(0));
  dumpChild(pass, pass->current->add_type_parts(), this->getContainedType(1));
}

void CArrayTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::CARRAY);
  pass->current->set_carray_size(this->getSize());
  dumpChild(pass, pass->current->add_type_parts(), this->getContainedType(0));
}

void TupleTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::TUPLE);
  pass->current->mutable_type_parts()->Reserve(this->getNumContainedTypes());
  for (int i = 0; i < this->getNumContainedTypes(); ++i) {
    ASSERT(this->getContainedType(i)) << "Unexpected NULL type when dumping TupleTypeAST " << str(this);
    dumpChild(pass, pass->current->add_type_parts(), this->getContainedType(i));
  }
}

