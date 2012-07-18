// Copyright (c) 2010 Ben Karel. All rights reserved.
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
// Thus, the way we transcribe our existing AST tree to protobufs
// is to store a "current parent pb::Expr*" as a field in the pass object;
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

void dumpKind(pb::Kind* target, const KindAST* kind) {
  if (const BaseKindAST* bk = dynamic_cast<const BaseKindAST*>(kind)) {
    switch (bk->kind) {
    case BaseKindAST::KindType: target->set_tag(pb::Kind::KIND_TYPE); break;
    case BaseKindAST::KindBoxed: target->set_tag(pb::Kind::KIND_BOXED); break;
    }
  } else {
    ASSERT(false) << "expected base kind in dumpKind()";
  }
}

void dumpTypeFormal(const TypeFormal* formal, pb::TypeFormal* target) {
  target->set_name(formal->name);
  ASSERT(formal->kind) << "Formal type parameter " << formal->name << " must have kind!";
  dumpKind(target->mutable_kind(), formal->kind);
}

/////////////////////////////////////////////////////////////////////

void dumpDataCtor(DataCtorAST* cc, pb::DataCtor* c) {
  c->set_name(cc->name);
  for (size_t i = 0; i < cc->types.size(); ++i) {
    ASSERT(cc->types[i] != NULL);
    DumpTypeToProtobufPass dt(c->add_type());
    cc->types[i]->dump(&dt);
  }
}

void dumpDataCtors(Data* dd, pb::DataType* d) {
 d->set_name(dd->name);
 for (size_t i = 0; i < dd->ctors.size(); ++i) {
   dumpDataCtor(dd->ctors[i], d->add_ctor());
 }
 for (size_t i = 0; i < dd->tyformals.size(); ++i) {
   dumpTypeFormal(&dd->tyformals[i], d->add_tyformal());
 }
}

void dumpModule(DumpToProtobufPass* pass,
                foster::fepb::SourceModule& sm, ModuleAST* mod) {
  sm.set_self_name(mod->name);
  sm.set_hash(mod->hash);

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

  for (size_t i = 0; i < mod->data_parts.size(); ++i) {
    dumpDataCtors(mod->data_parts[i], sm.add_data_type());
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

void StringAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::STRING);
  pass->current->set_string_value(this->stringValue);
}

void IntAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::PB_INT);
  pass->current->set_string_value(this->getOriginalText());
}

void RatAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::PB_RAT);
  pass->current->set_string_value(this->getOriginalText());
}

void VariableAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::VAR);
  pass->current->set_string_value(this->name);
}

void dumpFormal(DumpToProtobufPass* pass, pb::Formal* target,
                const Formal* formal) {
  target->set_name(formal->name);
  ASSERT(formal->type) << "Formal parameter " << formal->name << " must have type!";
  DumpTypeToProtobufPass dt(target->mutable_type());
  formal->type->dump(&dt);
}

void dumpValAbs(DumpToProtobufPass* pass, pb::PBValAbs* target,
                const ValAbs* valabs) {
  for (size_t i = 0; i < valabs->formals.size(); ++i) {
    dumpFormal(pass, target->add_formals(), &valabs->formals[i]);
  }
  for (size_t i = 0; i < valabs->tyVarFormals.size(); ++i) {
    dumpTypeFormal(&valabs->tyVarFormals[i], target->add_type_formals());
  }
  if (valabs->resultType) {
    ASSERT(false) << "result type annotations on functions aren't used.";
    //DumpTypeToProtobufPass dt(target->mutable_result_type());
    //valabs->resultType->dump(&dt);
  }
}

void ValAbs::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::VAL_ABS);
  if (this->name == "") {
    this->name = foster::ParsingContext::freshName("<anon_fn_");
  }
  pass->current->set_string_value(this->name);
  dumpValAbs(pass, pass->current->mutable_pb_val_abs(), this);
  dumpChild(pass, pass->current->add_parts(), this->parts[0]);
}

void IfExprAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::IF);
  pb::PBIf* if_ = pass->current->mutable_pb_if();
  dumpChild(pass, if_->mutable_test_expr(), this->getTestExpr());
  dumpChild(pass, if_->mutable_then_expr(), this->getThenExpr());
  dumpChild(pass, if_->mutable_else_expr(), this->getElseExpr());
}

void UntilExpr::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::UNTIL);
  dumpChildren(pass, this);
}

void SeqAST::dump(DumpToProtobufPass* pass) {
  if (this->parts.size() == 1) {
    this->parts[0]->dump(pass);
  } else {
    processExprAST(pass->current, this, pb::Expr::SEQ);
    dumpChildren(pass, this);
  }
}

void LetAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::LET);
  pb::PBLet* let_ = pass->current->mutable_pb_let();
  let_->set_is_recursive(this->isRecursive);
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

void CallPrimAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::CALLPRIM);
  pass->current->set_string_value(this->primname);
  dumpChildren(pass, this);
}

void ETypeAppAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::TY_APP);
  dumpChildren(pass, this);

  pass->current->mutable_ty_app_arg_type()->Reserve(this->typeArgs.size());
  for (size_t i = 0; i < this->typeArgs.size(); ++i) {
    DumpTypeToProtobufPass dt(pass->current->add_ty_app_arg_type());
    this->typeArgs[i]->dump(&dt);
  }
}

void BuiltinCompilesExprAST::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::COMPILES);
  if (this->parts[0] == NULL) {
    this->parts.clear();
  }
  dumpChildren(pass, this);
}

/////////////////////////////////////////////////////////////////////

void dumpPattern(DumpToProtobufPass* pass,
                 pb::Expr* target,
                 Pattern*  pat) {
  ASSERT(pat != NULL);
  pb::Expr* saved = pass->current;
  pass->current = target;
  pat->dump(pass);
  pass->current = saved;
}

void WildcardPattern::dump(DumpToProtobufPass* pass) {
  pass->current->set_tag(pb::Expr::PAT_WILDCARD);
  setSourceRange(pass->current->mutable_range(), this->sourceRange);
}

void LiteralPattern::dump(DumpToProtobufPass* pass) {
  setSourceRange(pass->current->mutable_range(), this->sourceRange);
  switch (variety) {
  case LP_VAR:  pass->current->set_tag(pb::Expr::PAT_VARIABLE); break;
  case LP_NUM:  pass->current->set_tag(pb::Expr::PAT_NUM);  break;
  case LP_BOOL: pass->current->set_tag(pb::Expr::PAT_BOOL); break;
  }

  dumpChild(pass, pass->current->add_parts(), this->pattern);
}

void CtorPattern::dump(DumpToProtobufPass* pass) {
  pass->current->set_tag(pb::Expr::PAT_CTOR);
  setSourceRange(pass->current->mutable_range(), this->sourceRange);
  pass->current->set_string_value(this->ctorName);

  std::vector<Pattern*>& parts = this->patterns;
  pass->current->mutable_parts()->Reserve(parts.size());
  for (size_t i = 0; i < parts.size(); ++i) {
    dumpPattern(pass, pass->current->add_parts(), parts[i]);
  }
}

void TuplePattern::dump(DumpToProtobufPass* pass) {
  pass->current->set_tag(pb::Expr::PAT_TUPLE);
  setSourceRange(pass->current->mutable_range(), this->sourceRange);

  std::vector<Pattern*>& parts = this->patterns;
  pass->current->mutable_parts()->Reserve(parts.size());
  for (size_t i = 0; i < parts.size(); ++i) {
    dumpPattern(pass, pass->current->add_parts(), parts[i]);
  }
}

void CaseExpr::dump(DumpToProtobufPass* pass) {
  processExprAST(pass->current, this, pb::Expr::CASE_EXPR);
  pb::PBCase* c = pass->current->mutable_pb_case();
  dumpChild(pass, c->mutable_scrutinee(), this->parts[0]);
  for (size_t i = 0; i < this->branches.size(); ++i) {
    CaseBranch b = this->branches[i];
    dumpPattern(pass, c->add_pattern(), b.first);
    dumpChild(  pass, c->add_branch(), b.second);
  }
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

void PrimitiveTypeAST::dump(DumpTypeToProtobufPass* pass) {
  ASSERT(false) << "no dumping primitive types";
}

void NamedTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::TYVAR);
  pass->current->set_name(this->name);
  pass->current->set_is_placeholder(this->is_placeholder);
}

void DataTypeAST::dump(DumpTypeToProtobufPass* pass) {
  ASSERT(false) << "data types should be handled after initial parsing";
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

void ArrayTypeAST::dump(DumpTypeToProtobufPass* pass) {
  ASSERT(false);
}

void TupleTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::TUPLE);
  pass->current->mutable_type_parts()->Reserve(this->getNumContainedTypes());
  for (int i = 0; i < this->getNumContainedTypes(); ++i) {
    ASSERT(this->getContainedType(i)) << "Unexpected NULL type when dumping TupleTypeAST " << str(this);
    dumpChild(pass, pass->current->add_type_parts(), this->getContainedType(i));
  }
}

void StructTypeAST::dump(DumpTypeToProtobufPass* pass) {
  ASSERT(false) << "no support yet for dumping struct types to protobufs";
}

void TypeTypeAppAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::TYPE_TYP_APP);
  pass->current->mutable_type_parts()->Reserve(this->getNumContainedTypes());
  for (int i = 0; i < this->getNumContainedTypes(); ++i) {
    ASSERT(this->getContainedType(i)) << "Unexpected NULL type when dumping TypeTypeAppAST " << str(this);
    dumpChild(pass, pass->current->add_type_parts(), this->getContainedType(i));
  }
}

void ForallTypeAST::dump(DumpTypeToProtobufPass* pass) {
  setTagAndRange(pass->current, this, pb::Type::FORALL_TY);
  pass->current->mutable_tyformals()->Reserve(this->tyformals.size());
  for (size_t i = 0; i < this->tyformals.size(); ++i) {
    dumpTypeFormal(&this->tyformals[i], pass->current->add_tyformals());
  }
  pass->current->mutable_type_parts()->Reserve(1);
  dumpChild(pass, pass->current->add_type_parts(), this->quant);
}

