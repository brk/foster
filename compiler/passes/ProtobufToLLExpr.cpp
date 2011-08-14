// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/SourceRange.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"
#include "parse/FosterTypeAST.h"
#include "parse/ProtobufToLLExpr.h"
#include "parse/FosterLL.h"
#include "base/LLVMUtils.h"

#include <sstream>

#include "pystring/pystring.h"

#include "_generated_/FosterIL.pb.h"

#include <vector>

struct LLExpr;

namespace foster {

namespace bepb {
  struct Expr;
  struct Type;
} // namespace foster::bepb

LLExpr* LLExpr_from_pb(const bepb::Expr*);
LLVar*  LLVar_from_pb(const bepb::Expr* pb) {
  LLExpr* e = LLExpr_from_pb(pb);
  LLVar* rv = dynamic_cast<LLVar*>(e);
  ASSERT(rv) << "Expected var, got " << e->tag;
  return rv;
}

TypeAST* TypeAST_from_pb(const bepb::Type*);
FnTypeAST* parseProcType(const bepb::ProcType&);

}

using foster::currentErrs;

using std::string;
using std::vector;

namespace pb = foster::bepb;

namespace foster {

// In LLVMUtils.cpp
extern std::map<std::string, std::string> sgProcLines;

namespace {

CtorId parseCtorId(const pb::PbCtorId& c) { CtorId x;
  x.typeName = c.ctor_type_name();
  x.ctorName = c.ctor_ctor_name();
  x.smallId = c.ctor_local_id();
  return x;
}

LLExpr* parseBool(const pb::Expr& e) {
  return new LLBool(e.bool_value() ? "true" : "false");
}

LLExpr* parseCall(const pb::Expr& e) {
  ASSERT(e.parts_size() >= 1);

  LLExpr* base = LLExpr_from_pb(&e.parts(0));
  std::vector<LLVar*> args;
  for (int i = 1; i < e.parts_size(); ++i) {
    args.push_back(LLVar_from_pb(&e.parts(i)));
  }
  bool callMayTriggerGC = e.call_may_trigger_gc();
  return new LLCall(base, args, callMayTriggerGC);
}

LLExpr* parseCallPrimOp(const pb::Expr& e) {
  ASSERT(e.parts_size() >= 1);
  std::vector<LLVar*> args;
  for (int i = 0; i < e.parts_size(); ++i) {
    args.push_back(LLVar_from_pb(&e.parts(i)));
  }
  return new LLCallPrimOp(e.name(), args);
}

LLExpr* parseAppCtor(const pb::Expr& e) {
  ASSERT(e.has_ctor_id()) << "APP_CTOR without ctor id?";
  std::vector<LLVar*> vars;
  for (int i = 0; i < e.parts_size(); ++i) {
    vars.push_back(LLVar_from_pb(&e.parts(i)));
  }
  return new LLAppCtor(parseCtorId(e.ctor_id()), vars);
}

LLExpr* parseIf(const pb::Expr& e) {
  ASSERT(e.has_pb_if());

  const pb::PBIf& i = e.pb_if();

  return new LLIf(
       LLVar_from_pb(& i.test_expr()),
      LLExpr_from_pb(& i.then_expr()),
      LLExpr_from_pb(& i.else_expr()));
}

LLExpr* parseInt(const pb::Expr& e) {
  if (!e.has_pb_int()) return NULL;
  const pb::PBInt& i = e.pb_int();
  return new LLInt(i.clean(), i.bits());
}

LLAllocate* parseAllocate(const pb::Expr& e) {
  ASSERT(e.has_alloc_info());
  const pb::AllocInfo& a = e.alloc_info();
  LLVar* array_size = NULL;

  if (a.has_array_size()) {
    array_size = LLVar_from_pb(&a.array_size());
  }

  LLAllocate::MemRegion target_region = LLAllocate::MEM_REGION_STACK;
  switch (a.mem_region()) {
  case             pb::AllocInfo::MEM_REGION_STACK:
      target_region = LLAllocate::MEM_REGION_STACK; break;
  case             pb::AllocInfo::MEM_REGION_GLOBAL_HEAP:
      target_region = LLAllocate::MEM_REGION_GLOBAL_HEAP; break;
  default: ASSERT(false) << "Unknown target region for AllocInfo.";
  }
  int8_t bogusCtorId = -2;
  bool unboxed = a.unboxed();
  return new LLAllocate(TypeAST_from_pb(& e.type()), bogusCtorId,
                        unboxed, array_size, target_region);
}

LLTuple* parseTuple(const pb::Expr& e) {
  std::vector<LLVar*> args;
  for (int i = 0; i < e.parts_size(); ++i) {
    args.push_back(LLVar_from_pb(&e.parts(i)));
  }
  return new LLTuple(args, parseAllocate(e));
}

LLClosure* parseClosure(const pb::Closure& clo) {
  return new LLClosure(clo.varname(), clo.envid(), clo.procid(),
                       parseTuple(clo.env()));
}

LLExpr* parseClosures(const pb::Expr& e) {
  ASSERT(e.parts_size() == 1) << "parseClosures needs 1 subexpr";
  std::vector<LLClosure*> closures;
  for (int i = 0; i < e.closures_size(); ++i) {
    closures.push_back(parseClosure(e.closures(i)));
  }
  return new LLClosures(LLExpr_from_pb(&e.parts(0)),
                        closures);
}

LLExpr* parseLetVals(const pb::Expr& e) {
  ASSERT(e.parts_size() == e.names_size() + 1);
  ASSERT(e.parts_size() >= 2) << "parseLetVal needs at least 2 subexprs";
  std::vector<std::string> names;
  std::vector<LLExpr*>     exprs;
  for (int i = 0; i < e.names_size(); ++i) {
    names.push_back(e.names(i));
    exprs.push_back(LLExpr_from_pb(&e.parts(i + 1)));
  }
  // let nm[0] = p[1] in
  // let nm[N] = p[N+1] in p[0]
  return new LLLetVals(names, exprs, LLExpr_from_pb(&e.parts(0)));
}

llvm::GlobalValue::LinkageTypes
parseLinkage(const pb::Proc::Linkage linkage) {
  switch (linkage) {
  case pb::Proc::Internal: return llvm::GlobalValue::InternalLinkage;
  case pb::Proc::External: return llvm::GlobalValue::ExternalLinkage;
  default: ASSERT(false) << "unknown linkage!";
           return llvm::GlobalValue::InternalLinkage;
  }
}

LLProc* parseProc(const pb::Proc& e) {
  ASSERT(e.has_proctype()) << "protobuf LLProc missing proc type!";

  FnTypeAST* proctype = parseProcType(e.proctype());

  std::vector<std::string> args;
  for (int i = 0; i < e.in_args_size(); ++i) {
    args.push_back(e.in_args(i));
  }

  foster::sgProcLines[e.name()] = e.lines();

  return new LLProc(proctype, e.name(), args,
                    parseLinkage(e.linkage()),
                    LLExpr_from_pb(& e.body()));
}

/*
LLExpr* parseSimd(const pb::Expr& e) {
  return new SimdVectorAST(LLExpr_from_pb(& e.parts(0)), range);
}
*/

LLExpr* parseArrayRead(const pb::Expr& e) {
  ASSERT(e.parts_size() == 2) << "array_read must have base and index";
  return new LLArrayRead(
       LLVar_from_pb(& e.parts(0)),
       LLVar_from_pb(& e.parts(1)));
}

LLExpr* parseArrayPoke(const pb::Expr& e) {
  ASSERT(e.parts_size() == 3) << "array_write must have value, base and index";
  return new LLArrayPoke(
       LLVar_from_pb(& e.parts(0)),
       LLVar_from_pb(& e.parts(1)),
       LLVar_from_pb(& e.parts(2)));
}

LLExpr* parseUntil(const pb::Expr& e) {
  ASSERT(e.parts_size() == 2) << "until must have cond and body";
  return new LLUntil(
      LLExpr_from_pb(& e.parts(0)),
      LLExpr_from_pb(& e.parts(1)));
}

DecisionTree* parseDecisionTree(const pb::DecisionTree& dt);

Occurrence* parseOccurrence(const pb::PbOccurrence& o) {
  Occurrence* rv = new Occurrence;
  for (int i = 0; i < o.occ_offset_size(); ++i) {
    rv->offsets.push_back(o.occ_offset(i));
  }
  return rv;
}

SwitchCase* parseSwitchCase(const pb::PbSwitchCase& sc) {
  SwitchCase* rv = new SwitchCase;

  for (int i = 0; i < sc.ctors_size(); ++i) {
    rv->ctors.push_back(parseCtorId(sc.ctors(i)));
  }

  for (int i = 0; i < sc.trees_size(); ++i) {
    rv->trees.push_back(parseDecisionTree(sc.trees(i)));
  }

  if (sc.has_defcase()) {
    rv->defaultCase = parseDecisionTree(sc.defcase());
  } else {
    rv->defaultCase = NULL;
  }

  rv->occ = parseOccurrence(sc.occ());
  return rv;
}

DecisionTree* parseDecisionTree(const pb::DecisionTree& dt) {
  std::vector<DTBinding> binds;

  switch (dt.tag()) {
  case pb::DecisionTree::DT_FAIL:
     return new DecisionTree(DecisionTree::DT_FAIL);
  case pb::DecisionTree::DT_LEAF:
    for (int i = 0; i < dt.leaf_idents_size(); ++i) {
      binds.push_back(DTBinding(
                        dt.leaf_idents(i),
                        parseOccurrence(dt.leaf_idoccs(i))));
    }
    return new DecisionTree(DecisionTree::DT_LEAF,
                            binds,
                            LLExpr_from_pb(&dt.leaf_action()));
  case pb::DecisionTree::DT_SWAP:
    ASSERT(false) << "Shouldn't be codegenning DT_SWAP nodes!";
  case pb::DecisionTree::DT_SWITCH:
    SwitchCase* sc = parseSwitchCase(dt.switchcase());
    return new DecisionTree(DecisionTree::DT_SWITCH, sc);
  }
  foster::EDiag() << "parseDecisionTree returning null for tag " << dt.tag();
  return NULL;
}

LLExpr* parseCase(const pb::Expr& e) {
  DecisionTree* dt = parseDecisionTree(e.dt());
  return new LLCase(LLVar_from_pb(&e.parts(0)), dt,
                    TypeAST_from_pb(& e.type()));
}

LLExpr* parseCoroPrim(const pb::Expr& e) {
  const pb::CoroPrim& p = e.coro_prim();
  TypeAST* r = TypeAST_from_pb(& p.ret_type());
  TypeAST* a = TypeAST_from_pb(& p.arg_type());
  switch (e.tag()) {
  case pb::Expr::IL_CORO_INVOKE: return new LLCoroPrim("coro_invoke", r, a);
  case pb::Expr::IL_CORO_CREATE: return new LLCoroPrim("coro_create", r, a);
  case pb::Expr::IL_CORO_YIELD : return new LLCoroPrim("coro_yield",  r, a);
  default: return NULL;
  }
}

LLExpr* parseVar(const pb::Expr& e)          { return new LLVar(e.name()); }
LLExpr* parseGlobalSymbol(const pb::Expr& e) { return new LLGlobalSymbol(e.name()); }

LLExpr* parseAlloc(const pb::Expr& e) {
  return new LLAlloc(LLVar_from_pb(& e.parts(0)));
}

LLExpr* parseDeref(const pb::Expr& e) {
  return new LLDeref(LLVar_from_pb(& e.parts(0)));
}

LLExpr* parseStore(const pb::Expr& e) {
  return new LLStore(
      LLVar_from_pb(& e.parts(0)),
      LLVar_from_pb(& e.parts(1)));
}

} // unnamed namespace

////////////////////////////////////////////////////////////////////

LLDecl* parseDecl(const pb::Decl& e) {
  return new LLDecl(      e.name(),
        TypeAST_from_pb(& e.type()));
}

LLModule* LLModule_from_pb(const pb::Module& e) {
  string moduleName = e.modulename();

  // Walk the type declarations and add their types to the current scope.
  // In contrast, the value declarations are only for checking purposes; if
  // a value isn't in a Module we've imported, we can't magically summon it!
  std::vector<NamedTypeAST*> namedTypes;
  for (int i = 0; i < e.typ_decls_size(); ++i){
    namedTypes.push_back(new NamedTypeAST(e.typ_decls(i).name(), NULL,
                         foster::SourceRange::getEmptyRange()));
    ParsingContext::insertType(e.typ_decls(i).name(),
                               namedTypes.back());
  }
  std::vector<LLDecl*> datatype_decls;
  for (int i = 0; i < e.typ_decls_size(); ++i){
    LLDecl* d = parseDecl(e.typ_decls(i));
    namedTypes[i]->setNamedType(d->getType());
    datatype_decls.push_back(d);
  }

  std::vector<LLProc*> procs;
  for (int i = 0; i < e.procs_size(); ++i) {
    procs.push_back(parseProc(e.procs(i)));
  }

  std::vector<LLDecl*> vdecls;
  for (int i = 0; i < e.val_decls_size(); ++i) {
    vdecls.push_back(parseDecl(e.val_decls(i)));
  }

  return new LLModule(moduleName, procs, vdecls, datatype_decls);
}


LLExpr* LLExpr_from_pb(const pb::Expr* pe) {
  if (!pe) return NULL;
  const pb::Expr& e = *pe;

  LLExpr* rv = NULL;

  switch (e.tag()) {
  case pb::Expr::IL_BOOL:        rv = parseBool(e); break;
  case pb::Expr::IL_CALL:        rv = parseCall(e); break;
  case pb::Expr::IL_CALL_PRIMOP: rv = parseCallPrimOp(e); break;
  case pb::Expr::IL_CTOR:        rv = parseAppCtor(e); break;
  case pb::Expr::IL_CASE:        rv = parseCase(e); break;
  case pb::Expr::IL_IF:          rv = parseIf(e); break;
  case pb::Expr::IL_INT:         rv = parseInt(e); break;
  case pb::Expr::IL_GLOBAL_SYMBOL:rv = parseGlobalSymbol(e); break;
  case pb::Expr::IL_LETVALS:     rv = parseLetVals(e); break;
  case pb::Expr::IL_CLOSURES:    rv = parseClosures(e); break;
  case pb::Expr::IL_UNTIL:       rv = parseUntil(e); break;
  //case pb::Expr::IL_SIMD:        rv = parseSimd(e); break;
  case pb::Expr::IL_CORO_INVOKE: rv = parseCoroPrim(e); break;
  case pb::Expr::IL_CORO_CREATE: rv = parseCoroPrim(e); break;
  case pb::Expr::IL_CORO_YIELD : rv = parseCoroPrim(e); break;
  case pb::Expr::IL_MEMALLOC:    rv = parseAllocate(e); break;
  case pb::Expr::IL_ALLOC:       rv = parseAlloc(e); break;
  case pb::Expr::IL_DEREF:       rv = parseDeref(e); break;
  case pb::Expr::IL_STORE:       rv = parseStore(e); break;
  case pb::Expr::IL_ARRAY_READ:  rv = parseArrayRead(e); break;
  case pb::Expr::IL_ARRAY_POKE:  rv = parseArrayPoke(e); break;
  case pb::Expr::IL_TUPLE:       rv = parseTuple(e); break;
  case pb::Expr::IL_VAR:         rv = parseVar(e); break;

  default:
    EDiag() << "Unknown protobuf tag: " << e.tag();
    break;
  }

  if (!rv) {
    EDiag() << "Unable to reconstruct LLExpr from protobuf Expr"
            << " with tag # " << e.tag() << ":"
            << "'" << e.DebugString() << "'";
  } else if (e.has_type()) {
    rv->type = TypeAST_from_pb(& e.type());
  }

  return rv;
}

FnTypeAST* parseProcType(const bepb::ProcType& fnty) {
  ASSERT(fnty.has_ret_type()) << "\n\tCannot build FnTypeAST without a return type in the protobuf";
  TypeAST* retTy = TypeAST_from_pb(&fnty.ret_type());
  ASSERT(retTy) << "\n\tCannot build FnTypeAST if the protobuf's"
     << " return type can't be reconstructed:\n"
     << fnty.ret_type().DebugString();

  std::vector<TypeAST*> argTypes(fnty.arg_types_size());
  for (size_t i = 0; i < argTypes.size(); ++i) {
    argTypes[i] = TypeAST_from_pb(&fnty.arg_types(i));
  }

  ASSERT(fnty.has_calling_convention())
    << "must provide calling convention for all function types!";
  std::map<std::string, std::string> annots;
  annots["callconv"] = fnty.calling_convention();
  return new FnTypeAST(retTy, argTypes, annots);
}


DataCtor* parseDataCtor(const pb::PbDataCtor* ct) {
  DataCtor* c = new DataCtor;
  c->name = ct->name();
  for (int i = 0; i < ct->type_size(); ++i) {
    c->types.push_back(TypeAST_from_pb(& ct->type(i)));
  }
  return c;
}

std::vector<DataCtor*> parseDataCtors(const pb::Type& t) {
  std::vector<DataCtor*> rv;
  for (int i = 0; i < t.ctor_size(); ++i) {
    rv.push_back(parseDataCtor(& t.ctor(i)));
  }
  return rv;
}

TypeAST* TypeAST_from_pb(const pb::Type* pt) {
  if (!pt) return NULL;
  const pb::Type& t = *pt;

  if (t.tag() == pb::Type::ARRAY) {
    return ArrayTypeAST::get(TypeAST_from_pb(&t.type_parts(0)));
  }

  if (t.tag() == pb::Type::PTR) {
    return RefTypeAST::get(TypeAST_from_pb(&t.type_parts(0)));
  }

  if (t.tag() == pb::Type::PROC) {
    FnTypeAST* fnty = parseProcType(t.procty());
    fnty->markAsProc();
    return fnty;
  }

  if (t.tag() == pb::Type::CLOSURE) {
    FnTypeAST* fnty = parseProcType(t.procty());
    fnty->markAsClosure();
    return fnty;
  }

  if (t.tag() == pb::Type::TUPLE) {
    std::vector<TypeAST*> parts(t.type_parts_size());
    for (size_t i = 0; i < parts.size(); ++i) {
      parts[i] = TypeAST_from_pb(&t.type_parts(i));
    }
    return TupleTypeAST::get(parts);
  }

  if (t.tag() == pb::Type::CORO) {
    TypeAST* targ = NULL;
    TypeAST* tret = NULL;
    ASSERT(t.type_parts_size() == 2)
        << "coro must have base and arg types,"
        << " but #type parts is " << t.type_parts_size();
    targ = TypeAST_from_pb(&t.type_parts(0));
    tret = TypeAST_from_pb(&t.type_parts(1));
    return CoroTypeAST::get(targ, tret);
  }

  if (t.tag() == pb::Type::LLVM_NAMED) {
    const string& tyname = t.name();

    ASSERT(!tyname.empty()) << "empty type name, probably implies a\n"
                  << "missing pb.if_X() check before pb.X().\n"
                  << "Use gdb to find the culprit.";

    TypeAST* rv = NULL;
    if (!tyname.empty() && tyname != "<NULL Ty>") {
      rv = foster::TypeASTFor(tyname);
    }
    ASSERT(rv) << "unable to find type named " << tyname;
    return rv;
  }

  if (t.tag() == pb::Type::TYPE_VARIABLE) {
    const string& tyname = t.name();
    return TypeVariableAST::get(tyname, SourceRange::getEmptyRange());
  }

  if (t.tag() == pb::Type::DATATYPE) {
    const string& tyname = t.name();
    return new DataTypeAST(tyname, parseDataCtors(t),
                           SourceRange::getEmptyRange());
  }

  EDiag() << "Error: found unexpected type in protobuf!\n" << t.DebugString();

  return NULL;
}

} // namespace foster

