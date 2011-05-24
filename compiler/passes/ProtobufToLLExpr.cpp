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

TypeAST* TypeAST_from_pb(const bepb::Type*);
FnTypeAST* parseProcType(const bepb::ProcType&);

}

using foster::currentErrs;

using std::string;
using std::vector;

namespace pb = foster::bepb;

namespace foster {

namespace {

LLExpr* parseBool(const pb::Expr& e) {
  return new LLBool(e.bool_value() ? "true" : "false");
}

LLExpr* parseCall(const pb::Expr& e) {
  ASSERT(e.parts_size() >= 1);

  LLVar* base = dynamic_cast<LLVar*>(LLExpr_from_pb(&e.parts(0)));
  std::vector<LLVar*> args;
  for (int i = 1; i < e.parts_size(); ++i) {
    LLExpr* expr = LLExpr_from_pb(&e.parts(i));
    LLVar* var = dynamic_cast<LLVar*>(expr);
    ASSERT(var != NULL) << "args to LLCall must be vars! got"
                        << pb::Expr::Tag_Name(e.parts(i).tag());
    args.push_back(var);
  }
  return new LLCall(base, args);
}

LLExpr* parseIf(const pb::Expr& e) {
  ASSERT(e.has_pb_if());

  const pb::PBIf& i = e.pb_if();

  return new LLIf(
      LLExpr_from_pb(& i.test_expr()),
      LLExpr_from_pb(& i.then_expr()),
      LLExpr_from_pb(& i.else_expr()));
}

LLExpr* parseInt(const pb::Expr& e) {
  if (!e.has_pb_int()) return NULL;
  const pb::PBInt& i = e.pb_int();
  return new LLInt(i.clean(), i.bits());
}

LLClosure* parseClosure(const pb::Closure& clo) {
  std::vector<std::string> varnames;
  for (int i = 0; i < clo.varnames_size(); ++i) {
    varnames.push_back(clo.varnames(i));
  }
  return new LLClosure(clo.varname(), clo.procid(), varnames);
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
  int N = e.names_size() - 1;
  LLExpr* letval = new LLLetVal(e.names(N),
                                LLExpr_from_pb(&e.parts(N+1)),
                                LLExpr_from_pb(&e.parts(0)));
  // let nm[0] = p[1] in
  // let nm[N] = p[N+1] in p[0]
  while (N --> 0) {
    letval = new LLLetVal(e.names(N), LLExpr_from_pb(&e.parts(N+1)), letval);
  }

  return letval;
}

LLProc* parseProc(const pb::Proc& e) {
  ASSERT(e.has_proctype()) << "protobuf LLProc missing proc type!";

  FnTypeAST* proctype = parseProcType(e.proctype());

  std::vector<std::string> args;
  for (int i = 0; i < e.in_args_size(); ++i) {
    args.push_back(e.in_args(i));
  }

  const std::string& name = e.name();
  return new LLProc(proctype, name, args,
                    LLExpr_from_pb(& e.body()));
}

/*
LLExpr* parseSimd(const pb::Expr& e) {
  return new SimdVectorAST(LLExpr_from_pb(& e.parts(0)), range);
}
*/

LLExpr* parseSubscript(const pb::Expr& e) {
  ASSERT(e.parts_size() == 2) << "subscript must have base and index";
  return new LLSubscript(
      LLExpr_from_pb(& e.parts(0)),
      LLExpr_from_pb(& e.parts(1)));
}

LLExpr* parseTuple(const pb::Expr& e) {
  std::vector<LLExpr*> args;
  for (int i = 0; i < e.parts_size(); ++i) {
    args.push_back(LLExpr_from_pb(&e.parts(i)));
  }
  LLTuple* rv = new LLTuple(args);
  rv->isClosureEnvironment = e.is_closure_environment();
  return rv;
}

LLCoroInvoke* parseCoroInvoke(const pb::CoroPrim& e) {
  return new LLCoroInvoke(
      TypeAST_from_pb(& e.ret_type()),
      TypeAST_from_pb(& e.arg_type()));
}

LLExpr* parseCoroInvoke(const pb::Expr& e) {
  ASSERT(e.has_coro_prim());
  return parseCoroInvoke(e.coro_prim());
}


LLCoroCreate* parseCoroCreate(const pb::CoroPrim& e) {
  return new LLCoroCreate(
      TypeAST_from_pb(& e.ret_type()),
      TypeAST_from_pb(& e.arg_type()));
}

LLExpr* parseCoroCreate(const pb::Expr& e) {
  ASSERT(e.has_coro_prim());
  return parseCoroCreate(e.coro_prim());
}

LLExpr* parseVar(const pb::Expr& e) {
  return new LLVar(e.name());
}


LLExpr* parseAlloc(const pb::Expr& e) {
  return new LLAlloc(LLExpr_from_pb(& e.parts(0)));
}

LLExpr* parseDeref(const pb::Expr& e) {
  return new LLDeref(LLExpr_from_pb(& e.parts(0)));
}


LLExpr* parseStore(const pb::Expr& e) {
  return new LLStore(
      LLExpr_from_pb(& e.parts(0)),
      LLExpr_from_pb(& e.parts(1)));
}

} // unnamed namespace

////////////////////////////////////////////////////////////////////

LLModule* LLModule_from_pb(const pb::Module& e) {
  string moduleName = e.modulename();
  std::vector<LLProc*> procs;
  for (int i = 0; i < e.procs_size(); ++i) {
    procs.push_back(parseProc(e.procs(i)));
  }
  return new LLModule(moduleName, procs);
}


LLExpr* LLExpr_from_pb(const pb::Expr* pe) {
  if (!pe) return NULL;
  const pb::Expr& e = *pe;

  LLExpr* rv = NULL;

  switch (e.tag()) {
  case pb::Expr::IL_BOOL:      rv = parseBool(e); break;
  case pb::Expr::IL_CALL:      rv = parseCall(e); break;
  case pb::Expr::IL_IF:        rv = parseIf(e); break;
  case pb::Expr::IL_INT:       rv = parseInt(e); break;
  case pb::Expr::IL_LETVALS:   rv = parseLetVals(e); break;
  case pb::Expr::IL_CLOSURES:  rv = parseClosures(e); break;
//  case pb::Expr::SIMD:      rv = parseSimd(e); break;
  case pb::Expr::IL_CORO_INVOKE: rv = parseCoroInvoke(e); break;
  case pb::Expr::IL_CORO_CREATE: rv = parseCoroCreate(e); break;
  case pb::Expr::IL_ALLOC:     rv = parseAlloc(e); break;
  case pb::Expr::IL_DEREF:     rv = parseDeref(e); break;
  case pb::Expr::IL_STORE:     rv = parseStore(e); break;
  case pb::Expr::IL_SUBSCRIPT: rv = parseSubscript(e); break;
  case pb::Expr::IL_TUPLE:     rv = parseTuple(e); break;
  case pb::Expr::IL_VAR:       rv = parseVar(e); break;

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
   std::string callingConvention = fnty.calling_convention();

  return FnTypeAST::get(retTy, argTypes, callingConvention);
}

TypeAST* TypeAST_from_pb(const pb::Type* pt) {
  if (!pt) return NULL;
  const pb::Type& t = *pt;

  if (t.tag() == pb::Type::PTR) {
    return RefTypeAST::get(TypeAST_from_pb(&t.type_parts(0)));
  }

  if (t.tag() == pb::Type::PROC) {
    return parseProcType(t.procty());
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
    return rv;
  }

  if (t.tag() == pb::Type::TYPE_VARIABLE) {
    const string& tyname = t.name();
    return TypeVariableAST::get(tyname, SourceRange::getEmptyRange());
  }

  EDiag() << "Error: found unexpected type in protobuf!\n" << t.DebugString();

  return NULL;
}

} // namespace foster

