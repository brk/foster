// Copyright (c) 2010 Fen Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterAST.h"
#include "passes/DumpToProtobuf.h"
#include "llvm/System/Path.h"

// Protobufs do not easily allow mirroring of existing object
// graph structures, because repeated (pointer) fields only allow
// adding child nodes by requesting new nodes from the parent,
// and do not directly support adopting existing nodes as children.
//
// Thus, the way we'll transcribe our existing AST tree to protobufs
// is to store a "current parent pb::Expr*" as a pass field;
// each leaf will initialize the current node with its data,
// and interior nodes will reset the current pointer with newly-created
// pb::Expr*s before recursing to child nodes.


void dumpChild(DumpToProtobufPass* pass,
               foster::pb::Expr* target,
               ExprAST* child) {
  foster::pb::Expr* saved = pass->current;
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

void setSourceLocation(foster::pb::SourceLocation* pbloc,
                       const foster::SourceLocation& loc) {
  pbloc->set_column(loc.column);
  pbloc->set_line(loc.line);
}

void setSourceRange(foster::pb::SourceRange* pbr,
                    const foster::SourceRange& r) {
  if (r.source) {
    llvm::sys::Path p(r.source->getPath());
    p.makeAbsolute(); // TODO perhaps all paths should be stored absolute...?
    pbr->set_file_path(p.str());
  }

  setSourceLocation(pbr->mutable_begin(), r.begin);
  setSourceLocation(pbr->mutable_end(),   r.end);
}

void processExprAST(foster::pb::Expr* current,
                    ExprAST* ast,
                    foster::pb::Expr::Tag tag) {
  current->set_tag(tag);
  setSourceRange(current->mutable_range(), ast->sourceRange);
}

/////////////////////////////////////////////////////////////////////

void DumpToProtobufPass::visit(BoolAST* ast)                {
  processExprAST(current, ast, foster::pb::Expr::BOOL);
  current->set_bool_value(ast->boolValue);
}

void DumpToProtobufPass::visit(IntAST* ast)                 {
  processExprAST(current, ast, foster::pb::Expr::INT);
  foster::pb::Int* int_ = current->mutable_int_();
  int_->set_base(ast->Base);
  int_->set_clean(ast->Clean);
  int_->set_text(ast->Text);
}

void DumpToProtobufPass::visit(VariableAST* ast)            {
  processExprAST(current, ast, foster::pb::Expr::VAR);
  current->set_name(ast->name);
}

void DumpToProtobufPass::visit(UnaryOpExprAST* ast)         {
  processExprAST(current, ast, foster::pb::Expr::OP);
  current->set_name(ast->op);
  dumpChildren(this, ast);
}

void DumpToProtobufPass::visit(BinaryOpExprAST* ast)        {
  processExprAST(current, ast, foster::pb::Expr::OP);
  current->set_name(ast->op);
  dumpChildren(this, ast);
}

void DumpToProtobufPass::visit(PrototypeAST* ast)           {
  processExprAST(current, ast, foster::pb::Expr::PROTO);
  foster::pb::Proto* proto = current->mutable_proto();
  proto->set_name(ast->name);

  proto->mutable_in_args()->Reserve(ast->parts.size());
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    dumpChild(this, proto->add_in_args(), ast->inArgs[i]);
  }
}
void DumpToProtobufPass::visit(FnAST* ast)                  {
  processExprAST(current, ast, foster::pb::Expr::FN);
  foster::pb::Fn* fn = current->mutable_fn();
  dumpChild(this, fn->mutable_proto(), ast->proto);
  dumpChild(this, fn->mutable_body(), ast->body);
  fn->set_lambda_lift_only(ast->lambdaLiftOnly);
  fn->set_was_nested(ast->wasNested);
}
void DumpToProtobufPass::visit(ClosureAST* ast) {
  processExprAST(current, ast, foster::pb::Expr::CLOSURE);
  foster::pb::Closure* clo = current->mutable_closure();
  if (ast->fn) {
    dumpChild(this, clo->mutable_fn(), ast->fn);
  }
}
void DumpToProtobufPass::visit(ModuleAST* ast)              {
  processExprAST(current, ast, foster::pb::Expr::MODULE);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(IfExprAST* ast)              {
  processExprAST(current, ast, foster::pb::Expr::IF);
  foster::pb::If* if_ = current->mutable_if_();
  dumpChild(this, if_->mutable_test_expr(), ast->testExpr);
  dumpChild(this, if_->mutable_then_expr(), ast->thenExpr);
  dumpChild(this, if_->mutable_else_expr(), ast->elseExpr);
}
void DumpToProtobufPass::visit(ForRangeExprAST* ast)              {
  processExprAST(current, ast, foster::pb::Expr::FORRANGE);
  foster::pb::ForRange* fr = current->mutable_for_range();
  dumpChild(this, fr->mutable_var(), ast->var);
  dumpChild(this, fr->mutable_start(), ast->startExpr);
  dumpChild(this, fr->mutable_end(), ast->endExpr);
  dumpChild(this, fr->mutable_body(), ast->bodyExpr);
  if (ast->incrExpr) {
    dumpChild(this, fr->mutable_incr(), ast->incrExpr);
  }
}
void DumpToProtobufPass::visit(NilExprAST* ast)             {
  processExprAST(current, ast, foster::pb::Expr::NIL);
}
void DumpToProtobufPass::visit(RefExprAST* ast)             {
  processExprAST(current, ast, foster::pb::Expr::REF);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(DerefExprAST* ast)           {
  processExprAST(current, ast, foster::pb::Expr::DEREF);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(AssignExprAST* ast)          {
  processExprAST(current, ast, foster::pb::Expr::ASSIGN);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(SubscriptAST* ast)           {
  processExprAST(current, ast, foster::pb::Expr::SUBSCRIPT);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(SimdVectorAST* ast)          {
  processExprAST(current, ast, foster::pb::Expr::SIMD);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(SeqAST* ast)                 {
  processExprAST(current, ast, foster::pb::Expr::SEQ);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(CallAST* ast)                {
  processExprAST(current, ast, foster::pb::Expr::CALL);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(ArrayExprAST* ast)           {
  llvm::errs() << "no support for dumping arrays to protobufs!\n";
}

void DumpToProtobufPass::visit(TupleExprAST* ast)           {
  processExprAST(current, ast, foster::pb::Expr::TUPLE);
  current->set_is_closure_environment(ast->isClosureEnvironment);
  dumpChildren(this, ast);
}
void DumpToProtobufPass::visit(BuiltinCompilesExprAST* ast) {
  processExprAST(current, ast, foster::pb::Expr::COMPILES);
  switch (ast->status) {
    case BuiltinCompilesExprAST::kNotChecked:
      break;
    case BuiltinCompilesExprAST::kWouldCompile:
      current->set_compiles(true); break;
    case BuiltinCompilesExprAST::kWouldNotCompile:
      current->set_compiles(false); break;
  }
}
