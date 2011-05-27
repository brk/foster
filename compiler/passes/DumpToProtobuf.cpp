// Copyright (c) 2010 Fen Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "base/LLVMUtils.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ParsingContext.h"
#include "passes/DumpToProtobuf.h"

#include "llvm/Support/Path.h"

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

void dumpChildren(DumpToProtobufPass* pass, ExprAST* ast) {
  std::vector<ExprAST*>& parts = ast->parts;
  pass->current->mutable_parts()->Reserve(parts.size());
  for (size_t i = 0; i < parts.size(); ++i) {
    dumpChild(pass, pass->current->add_parts(), parts[i]);
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

void dumpModule(DumpToProtobufPass* pass,
                foster::fepb::SourceModule& sm, ModuleAST* mod) {
  sm.set_name(mod->name);

  for (size_t i = 0; i < mod->decl_parts.size(); ++i) {
    pb::Decl* d = sm.add_decl();
    d->set_name(mod->decl_parts[i]->name);
    DumpTypeToProtobufPass dt(d->mutable_type());
    mod->decl_parts[i]->type->dump(&dt);
  }

  for (size_t i = 0; i < mod->defn_parts.size(); ++i) {
    pb::Defn* d = sm.add_defn();
    d->set_name(mod->defn_parts[i]->name);
    dumpChild(pass, d->mutable_body(), mod->defn_parts[i]->body);
  }

  if (const foster::InputTextBuffer* buf = mod->buf) {
    for (int i = 0; i < buf->getLineCount(); ++i) {
      sm.add_line(buf->getLine(i));
    }
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

void dumpFormal(DumpToProtobufPass* pass, pb::Formal* target, Formal* formal) {
  target->set_name(formal->name);
  ASSERT(formal->type) << "Formal parameter " << formal->name << " must have type!";
  DumpTypeToProtobufPass dt(target->mutable_type());
  formal->type->dump(&dt);
}

void ValAbs::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::VAL_ABS);
  if (this->name == "") {
    this->name = foster::ParsingContext::freshName("<anon_fn_");
  }
  pass->current->set_name(this->name);
  for (size_t i = 0; i < this->formals.size(); ++i) {
    dumpFormal(pass, pass->current->add_formals(), this->formals[i]);
  }
  dumpChild(pass, pass->current->add_parts(), this->parts[0]);
  if (this->resultType) {
    DumpTypeToProtobufPass dt(pass->current->mutable_result_type());
    this->resultType->dump(&dt);
  }
}

void IfExprAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::IF);
  pb::PBIf* if_ = pass->current->mutable_pb_if();
  dumpChild(pass, if_->mutable_test_expr(), this->getTestExpr());
  dumpChild(pass, if_->mutable_then_expr(), this->getThenExpr());
  dumpChild(pass, if_->mutable_else_expr(), this->getElseExpr());
}

void AllocAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::ALLOC);
  dumpChildren(pass, this);
}

void DerefAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::DEREF);
  dumpChildren(pass, this);
}

void StoreAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::STORE);
  dumpChildren(pass, this);
}

void SubscriptAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::SUBSCRIPT);
  dumpChildren(pass, this);
}

void SeqAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::SEQ);
  dumpChildren(pass, this);
}

void LetAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::LET);
  pb::PBLet* let_ = pass->current->mutable_pb_let();
  for (size_t i = 0; i < this->bindings.size(); ++i) {
    pb::TermBinding* b = let_->add_binding();
    b->set_name(this->bindings[i].name);
    dumpChild(pass, b->mutable_body(), this->bindings[i].body);
  }
  dumpChild(pass, let_->mutable_body(), this->parts[0]);
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
  dumpChildren(pass, this);
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
  //string tyname = str(this->getLLVMType());
  //ASSERT(!tyname.empty());
  //pass->current->set_name(tyname);
  pass->current->set_name(this->name);
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

