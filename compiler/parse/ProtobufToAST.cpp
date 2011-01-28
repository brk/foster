// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/SourceRange.h"
#include "base/PathManager.h"
#include "base/InputFile.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"
#include "parse/ProtobufToAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"
#include "base/LLVMUtils.h"

#include <sstream>

#include "pystring/pystring.h"

#include "_generated_/FosterAST.pb.h"

#include <vector>

using foster::currentErrs;

using std::string;
using std::vector;

void initSourceLocation(foster::SourceLocation& loc,
                        const foster::pb::SourceLocation* pbloc);

const char* getDefaultCallingConvProtoRecon() {
 // foster::EDiag() << "getDefaultCallingConvProtoRecon()";
  return foster::kDefaultFnLiteralCallingConvention;
}

template <typename PB>
void parseRangeFrom(foster::SourceRange& r, const PB& p) {
  foster::pb::SourceRange sr = p.range();
  initSourceLocation(const_cast<foster::SourceLocation&>(r.begin), sr.mutable_begin());
  initSourceLocation(const_cast<foster::SourceLocation&>(r.end  ), sr.mutable_end());

  r.source = NULL;

  if (sr.has_file_path()) {
    const std::string& pathstr = sr.file_path();
    llvm::sys::Path path = llvm::sys::Path(pathstr);

    if (path.isValid()) {
      makePathAbsolute(path);
      if (path.canRead()) {
        r.source = foster::gInputFileRegistry
                              .getOrCreateInputFileForAbsolutePath(path);
      }
    }
  } else {
    // No explicit file path -- use an implicit path?
    // TODO
  }
}

namespace foster {

namespace {

ExprAST* parseBool(const pb::Expr& e, const foster::SourceRange& range) {
  return new BoolAST(e.bool_value() ? "true" : "false", range);
}

ExprAST* parseCall(const pb::Expr& e, const foster::SourceRange& range) {
  ASSERT(e.parts_size() >= 1);

  ExprAST* base = ExprAST_from_pb(&e.parts(0));
  Exprs args;
  for (int i = 1; i < e.parts_size(); ++i) {
    args.push_back(ExprAST_from_pb(&e.parts(i)));
  }
  return new CallAST(base, args, range);
}

ExprAST* parseCompiles(const pb::Expr& e, const foster::SourceRange& range) {
  ASSERT(e.parts_size() == 1) << "CompilesExpr parts size: "
                              << e.parts_size();

  BuiltinCompilesExprAST* rv = new BuiltinCompilesExprAST(
                                          ExprAST_from_pb(& e.parts(0)), range);
  if (!e.has_compiles_status()) {
    llvm::outs() << "Warning: CompilesExpr had no status, using kNotChecked."
                 << "\n";
    rv->status = BuiltinCompilesExprAST::kNotChecked;
  } else if (e.compiles_status() == "kNotChecked") {
    rv->status = BuiltinCompilesExprAST::kNotChecked;
  } else if (e.compiles_status() == "kWouldCompile") {
    rv->status = BuiltinCompilesExprAST::kWouldCompile;
  } else if (e.compiles_status() == "kWouldNotCompile") {
    rv->status = BuiltinCompilesExprAST::kWouldNotCompile;
  } else {
    ASSERT(false) << "Unknown CompilesExpr status: "
                  << e.compiles_status() << "\n";
  }
  return rv;
}

ExprAST* parseFn(const pb::Expr& e, const foster::SourceRange& range) {
  ASSERT(e.parts_size() == 2) << "fn must have body and proto";

  PrototypeAST* proto = dynamic_cast<PrototypeAST*>(ExprAST_from_pb(& e.parts(0)));
  ExprAST* body = NULL;

  ExprAST::ScopeType* scope = gScope.pushScope(proto->getName());
    // Ensure all the function parameters are available in the function body.
    for (unsigned i = 0; i < proto->inArgs.size(); ++i) {
      scope->insert(proto->inArgs[i]->name, proto->inArgs[i]);
    }
    body = ExprAST_from_pb(& e.parts(1));
  gScope.popScope();

  FnAST* fn = new FnAST(proto, body, scope, range);
  if (e.has_is_closure() && e.is_closure()) {
    fn->markAsClosure();
  }

  return fn;
}

ExprAST* parseIf(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_pb_if()) return NULL;

  const pb::PBIf& i = e.pb_if();

  return new IfExprAST(
      ExprAST_from_pb(& i.test_expr()),
      ExprAST_from_pb(& i.then_expr()),
      ExprAST_from_pb(& i.else_expr()), range);
}

ExprAST* parseInt(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_pb_int()) return NULL;

  const pb::PBInt& i = e.pb_int();
  string text = i.originaltext();
  string clean = pystring::replace(text, "`", "");
  vector<string> parts;
  pystring::split(clean, parts, "_");
  int base = 10;
  if (parts.size() == 2) {
    clean = parts[0];
    std::stringstream ss; ss << parts[1]; ss >> base;
  }

  return foster::parseInt(clean, text, base, range);
}

ExprAST* parseModule(const pb::Expr& e, const foster::SourceRange& range) {
  string moduleName = e.name();
  Exprs args;
  for (int i = 0; i < e.parts_size(); ++i) {
    args.push_back(ExprAST_from_pb(&e.parts(i)));
  }
  return new ModuleAST(args,
                       moduleName,
                       gScope.getRootScope(),
                       range);
}

ExprAST* parseNamedTypeDecl(const pb::Expr& e, const foster::SourceRange& range) {
  ASSERT(e.has_name()) << "cannot reconstruct a named type without a name";
  // We pass NULL for the bound type, assuming that ExprAST_from_pb() will
  // assign the type field directly.
  return new NamedTypeDeclAST(e.name(), NULL, range);
}

ExprAST* parseProto(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_proto()) return NULL;

  const pb::Proto& proto = e.proto();
  std::vector<VariableAST*> args;
  for (int i = 0; i < proto.in_args_size(); ++i) {
    ExprAST* arg = ExprAST_from_pb(& proto.in_args(i));
    args.push_back(dynamic_cast<VariableAST*>(arg));
  }

  TypeAST* retTy = NULL;
  if (proto.has_result()) {
    retTy = TypeAST_from_pb(& proto.result());
  } else {
    EDiag() << "protobuf PrototypeAST missing ret type, using i32";
    retTy = TypeAST::i(32);
  }

  const std::string& name = proto.name();

  // TODO lexical scope?
  return new PrototypeAST(retTy, name, args, range);
}

ExprAST* parseSeq(const pb::Expr& e, const foster::SourceRange& range) {
  Exprs args;
  for (int i = 0; i < e.parts_size(); ++i) {
    args.push_back(ExprAST_from_pb(&e.parts(i)));
  }
  return new SeqAST(args, range);
}

/*
ExprAST* parseSimd(const pb::Expr& e, const foster::SourceRange& range) {
  return new SimdVectorAST(ExprAST_from_pb(& e.parts(0)), range);
}
*/

ExprAST* parseSubscript(const pb::Expr& e, const foster::SourceRange& range) {
  ASSERT(e.parts_size() == 2) << "subscript must have base and index";
  return new SubscriptAST(
      ExprAST_from_pb(& e.parts(0)),
      ExprAST_from_pb(& e.parts(1)), range);
}

ExprAST* parseTuple(const pb::Expr& e, const foster::SourceRange& range) {
  TupleExprAST* rv = new TupleExprAST(parseSeq(e, range), range);
  rv->isClosureEnvironment = e.is_closure_environment();
  return rv;
}

ExprAST* parseE_TyApp(const pb::Expr& e, const foster::SourceRange& range) {
  ASSERT(e.has_type()) << "TY_APP must have overall type";
  ASSERT(e.has_ty_app_arg_type()) << "TY_APP must have arg type";
  ASSERT(e.parts_size() == 1) << "TY_APP must have base";

  TypeAST* overallType = TypeAST_from_pb(&e.type());
  ExprAST* tyapp = new ETypeAppAST(
      overallType,
      ExprAST_from_pb(& e.parts(0)),
      TypeAST_from_pb(& e.ty_app_arg_type()), range);
  return tyapp;
}

ExprAST* parseVar(const pb::Expr& e, const foster::SourceRange& range) {
  TypeAST* ty = e.has_type() ? TypeAST_from_pb(&e.type()) : NULL;
  return new VariableAST(e.name(), ty, range);
}

} // unnamed namespace

ExprAST* ExprAST_from_pb(const pb::Expr* pe) {
  if (!pe) return NULL;
  const pb::Expr& e = *pe;

  foster::SourceRange range = foster::SourceRange::getEmptyRange();
  if (e.has_range()) {
    parseRangeFrom(range, e);
  }

  ExprAST* rv = NULL;

  switch (e.tag()) {
  case pb::Expr::BOOL:      rv = parseBool(e, range); break;
  case pb::Expr::CALL:      rv = parseCall(e, range); break;
  case pb::Expr::COMPILES:  rv = parseCompiles(e, range); break;
  case pb::Expr::FN:        rv = parseFn(e, range); break;
  case pb::Expr::IF:        rv = parseIf(e, range); break;
  case pb::Expr::PB_INT:    rv = parseInt(e, range); break;
  case pb::Expr::MODULE:    rv = parseModule(e, range); break;
  case pb::Expr::NAMED_TYPE_DECL: rv = parseNamedTypeDecl(e, range); break;
  case pb::Expr::PROTO:     rv = parseProto(e, range); break;
  case pb::Expr::SEQ:       rv = parseSeq(e, range); break;
//  case pb::Expr::SIMD:      rv = parseSimd(e, range); break;
  case pb::Expr::TY_APP:    rv = parseE_TyApp(e, range); break;
  case pb::Expr::SUBSCRIPT: rv = parseSubscript(e, range); break;
  case pb::Expr::TUPLE:     rv = parseTuple(e, range); break;
  case pb::Expr::VAR:       rv = parseVar(e, range); break;

  default:
    EDiag() << "Unknown protobuf tag: " << e.tag();
    break;
  }

  if (!rv) {
    EDiag() << "Unable to reconstruct ExprAST from protobuf Expr"
            << " with tag # " << e.tag() << ":"
            << "'" << e.DebugString() << "'";
  } else if (e.has_type()) {
    rv->type = TypeAST_from_pb(& e.type());
  }

  return rv;
}

TypeAST* TypeAST_from_pb(const pb::Type* pt) {
  if (!pt) return NULL;
  const pb::Type& t = *pt;

  foster::SourceRange range = foster::SourceRange::getEmptyRange();
  if (t.has_range()) {
    parseRangeFrom(range, t);
  }

  if (t.has_ref_underlying_type()) {
    TypeAST* baseType = TypeAST_from_pb(&t.ref_underlying_type());
    return RefTypeAST::get(baseType);
  }

  if (t.has_fnty()) {
    const foster::pb::FnType& fnty = t.fnty();

    ASSERT(fnty.has_ret_type()) << "\n\tCannot build FnTypeAST without a return type in the protobuf";
    TypeAST* retTy = TypeAST_from_pb(&fnty.ret_type());
    ASSERT(retTy) << "\n\tCannot build FnTypeAST if the protobuf's"
       << " return type can't be reconstructed:\n"
       << fnty.ret_type().DebugString();

    std::vector<TypeAST*> argTypes(fnty.arg_types_size());
    for (size_t i = 0; i < argTypes.size(); ++i) {
      argTypes[i] = TypeAST_from_pb(&fnty.arg_types(i));
    }

    std::string callingConvention = getDefaultCallingConvProtoRecon();
    if (fnty.has_calling_convention()) {
      callingConvention = fnty.calling_convention();
    }

    FnTypeAST* fty = FnTypeAST::get(retTy, argTypes, callingConvention);
    if (fnty.has_is_closure() && fnty.is_closure()) {
      fty->markAsClosure();
    }
    return fty;
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
    return TypeVariableAST::get(tyname, range);
  }

  currentErrs() << "Error: found unexpected type in protobuf!\n" << t.DebugString() << "\n";

  return NULL;
}

} // namespace foster


void initSourceLocation(foster::SourceLocation& loc,
                        const foster::pb::SourceLocation* pbloc) {
  if (!pbloc) {
    loc = foster::SourceLocation::getInvalidLocation();
  } else {
    loc.line = pbloc->line();
    loc.column = pbloc->column();
  }
}
