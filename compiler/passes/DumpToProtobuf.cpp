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
  child->accept(pass);
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
    ast->type->accept(&dt);
  }
}

/////////////////////////////////////////////////////////////////////

void DumpToProtobufPass::visit(BoolAST* ast)                {
  processExprAST(current, ast, pb::Expr::BOOL);
  current->set_bool_value(ast->boolValue);
}

void DumpToProtobufPass::visit(IntAST* ast)                 {
  processExprAST(current, ast, pb::Expr::PB_INT);
  current->set_int_text(ast->getOriginalText());
}

void DumpToProtobufPass::visit(VariableAST* ast)            {
  processExprAST(current, ast, pb::Expr::VAR);
  current->set_name(ast->name);
}

void DumpToProtobufPass::visit(PrototypeAST* ast)           {
  processExprAST(current, ast, pb::Expr::PROTO);
  pb::Proto* proto = current->mutable_proto();
  proto->set_name(ast->getName());

  proto->mutable_in_args()->Reserve(ast->parts.size());
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    dumpChild(this, proto->add_in_args(), ast->inArgs[i]);
  }

  if (ast->resultTy) {
    DumpTypeToProtobufPass dt(proto->mutable_result());
    ast->resultTy->accept(&dt);
  }
}

void DumpToProtobufPass::visit(FnAST* ast) {
  processExprAST(current, ast, pb::Expr::FN);
  dumpChild(this, this->current->add_parts(), ast->getProto());
  dumpChild(this, this->current->add_parts(), ast->parts[0]);
  this->current->set_is_closure(ast->isClosure());
}

void DumpToProtobufPass::visit(ModuleAST* ast)              {
  processExprAST(current, ast, pb::Expr::MODULE);
  current->set_name(ast->name);
  dumpChildren(this, ast);
}

void DumpToProtobufPass::visit(NamedTypeDeclAST* ast) {
  processExprAST(current, ast, pb::Expr::NAMED_TYPE_DECL);
  current->set_name(ast->name);
}

void DumpToProtobufPass::visit(IfExprAST* ast)              {
  processExprAST(current, ast, pb::Expr::IF);
  pb::PBIf* if_ = current->mutable_pb_if();
  dumpChild(this, if_->mutable_test_expr(), ast->getTestExpr());
  dumpChild(this, if_->mutable_then_expr(), ast->getThenExpr());
  dumpChild(this, if_->mutable_else_expr(), ast->getElseExpr());
}

void DumpToProtobufPass::visit(SubscriptAST* ast)           {
  processExprAST(current, ast, pb::Expr::SUBSCRIPT);
  dumpChildren(this, ast);
}

void DumpToProtobufPass::visit(SeqAST* ast)                 {
  processExprAST(current, ast, pb::Expr::SEQ);
  dumpChildren(this, ast);
}

void DumpToProtobufPass::visit(CallAST* ast)                {
  processExprAST(current, ast, pb::Expr::CALL);
  dumpChildren(this, ast);
}

void DumpToProtobufPass::visit(ETypeAppAST* ast)                {
  processExprAST(current, ast, pb::Expr::TY_APP);
  dumpChildren(this, ast);
  DumpTypeToProtobufPass dt(current->mutable_ty_app_arg_type());
  ast->typeArg->accept(&dt);
}

void DumpToProtobufPass::visit(TupleExprAST* ast)           {
  processExprAST(current, ast, pb::Expr::TUPLE);
  current->set_is_closure_environment(ast->isClosureEnvironment);
  ASSERT(ast->parts.size() == 1); // have a SeqAST wrapper...
  dumpChildren(this, ast->parts[0]);
}

void DumpToProtobufPass::visit(BuiltinCompilesExprAST* ast) {
  processExprAST(current, ast, pb::Expr::COMPILES);
  if (ast->parts[0] == NULL) {
    ast->parts.clear();
  }
  dumpChildren(this, ast);
}

/////////////////////////////////////////////////////////////////////

void dumpChild(DumpTypeToProtobufPass* pass,
               pb::Type* target,
               TypeAST* child) {
  if (!child) return;

  pb::Type* saved = pass->current;
  pass->current = target;
  child->accept(pass);
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


void DumpTypeToProtobufPass::visit(NamedTypeAST* ast) {
  setTagAndRange(current, ast, pb::Type::LLVM_NAMED);
  string tyname = str(ast->getLLVMType());
  ASSERT(!tyname.empty());
  current->set_name(tyname);
}

void DumpTypeToProtobufPass::visit(TypeVariableAST* ast) {
  setTagAndRange(current, ast, pb::Type::TYPE_VARIABLE);
  current->set_name(ast->getTypeVariableName());
}

void DumpTypeToProtobufPass::visit(FnTypeAST* ast) {
  setTagAndRange(current, ast, pb::Type::FN);

  pb::FnType* fnty = current->mutable_fnty();
  fnty->set_calling_convention(ast->getCallingConventionName());

  if (ast->getReturnType()) {
    dumpChild(this, fnty->mutable_ret_type(), ast->getReturnType());
  }

  fnty->mutable_arg_types()->Reserve(ast->getNumParams());
  for (int i = 0; i < ast->getNumParams(); ++i) {
    dumpChild(this, fnty->add_arg_types(), ast->getParamType(i));
  }

  fnty->set_is_closure(ast->isMarkedAsClosure());
}

void DumpTypeToProtobufPass::visit(RefTypeAST* ast) {
  setTagAndRange(current, ast, pb::Type::REF);

  if (ast->getElementType()) {
    dumpChild(this, current->mutable_ref_underlying_type(), ast->getElementType());
  }
}

void DumpTypeToProtobufPass::visit(CoroTypeAST* ast) {
  setTagAndRange(current, ast, pb::Type::CORO);
  dumpChild(this, current->add_type_parts(), ast->getContainedType(0));
  dumpChild(this, current->add_type_parts(), ast->getContainedType(1));
}

void DumpTypeToProtobufPass::visit(CArrayTypeAST* ast) {
  setTagAndRange(current, ast, pb::Type::CARRAY);
  current->set_carray_size(ast->getSize());
  dumpChild(this, current->add_type_parts(), ast->getContainedType(0));
}

void DumpTypeToProtobufPass::visit(TupleTypeAST* ast) {
  setTagAndRange(current, ast, pb::Type::TUPLE);
  current->mutable_type_parts()->Reserve(ast->getNumContainedTypes());
  for (int i = 0; i < ast->getNumContainedTypes(); ++i) {
    ASSERT(ast->getContainedType(i)) << "Unexpected NULL type when dumping TupleTypeAST " << str(ast);
    dumpChild(this, current->add_type_parts(), ast->getContainedType(i));
  }
}

