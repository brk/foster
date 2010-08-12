// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Diagnostics.h"
#include "base/SourceRange.h"
#include "base/PathManager.h"
#include "base/InputFile.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/CompilationContext.h"
#include "parse/ProtobufToAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterAST.h"

#include "pystring/pystring.h"

#include "_generated_/FosterAST.pb.h"

#include <vector>

using std::string;
using std::vector;

void initSourceLocation(foster::SourceLocation& loc,
                        const foster::pb::SourceLocation* pbloc);

template <typename PB>
void parseRangeFrom(foster::SourceRange& r, const PB& p) {
  foster::pb::SourceRange sr = p.range();
  initSourceLocation(const_cast<foster::SourceLocation&>(r.begin), sr.mutable_begin());
  initSourceLocation(const_cast<foster::SourceLocation&>(r.end  ), sr.mutable_end());

  r.source = NULL;

  if (sr.has_file_path()) {
    const std::string& pathstr = sr.file_path();
    llvm::sys::Path* path = new llvm::sys::Path(pathstr);

    if (path->isValid()) {
      path->makeAbsolute();
      if (path->canRead()) {
        r.source = foster::gInputFileRegistry
                              .getOrCreateInputFileForAbsolutePath(*path);
      }
    }
  } else {
    // No explicit file path -- use an implicit path?
    // TODO
  }
}

namespace foster {

#if 0
ModuleAST* ModuleAST_from_pb() {

}
#endif

namespace {


ExprAST* parseAssign(const pb::Expr& e, const foster::SourceRange& range) {
  return new AssignExprAST(
      ExprAST_from_pb(& e.parts(0)),
      ExprAST_from_pb(& e.parts(1)),
      range);
}

ExprAST* parseBool(const pb::Expr& e, const foster::SourceRange& range) {
  return new BoolAST(e.bool_value() ? "true" : "false", range);
}

ExprAST* parseCall(const pb::Expr& e, const foster::SourceRange& range) {
  ExprAST* base = ExprAST_from_pb(&e.parts(0));
  Exprs args;
  for (size_t i = 1; i < e.parts_size(); ++i) {
    args.push_back(ExprAST_from_pb(&e.parts(i)));
  }
  return new CallAST(base, args, range);
}

ExprAST* parseClosure(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_closure()) return NULL;

  const pb::Closure& c = e.closure();

  ClosureAST* clo = new ClosureAST(
      dynamic_cast<FnAST*>(ExprAST_from_pb(& c.fn())),
      range);

  clo->isTrampolineVersion = c.has_is_trampoline_version()
                          && c.is_trampoline_version();
  return clo;
}

ExprAST* parseCompiles(const pb::Expr& e, const foster::SourceRange& range) {
  BuiltinCompilesExprAST* rv = new BuiltinCompilesExprAST(
                                          ExprAST_from_pb(& e.parts(0)), range);
  if (e.has_compiles()) {
    rv->status = (e.compiles()) ? BuiltinCompilesExprAST::kWouldCompile
                                : BuiltinCompilesExprAST::kWouldNotCompile;
  } else {
    rv->status = BuiltinCompilesExprAST::kNotChecked;
  }
  return rv;
}

ExprAST* parseDeref(const pb::Expr& e, const foster::SourceRange& range) {
  return new DerefExprAST(ExprAST_from_pb(& e.parts(0)), range);
}

ExprAST* parseFn(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_fn()) return NULL;

  const pb::Fn& f = e.fn();

  FnAST* fn = new FnAST(
      dynamic_cast<PrototypeAST*>(ExprAST_from_pb(& f.proto())),
      ExprAST_from_pb(& f.body()),
      range);

  fn->wasNested = f.has_was_nested() && f.was_nested();
  fn->lambdaLiftOnly = f.has_lambda_lift_only() && f.lambda_lift_only();
  return fn;
}

ExprAST* parseForrange(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_for_range()) return NULL;

  const pb::ForRange& fr = e.for_range();
  return new ForRangeExprAST(
      dynamic_cast<VariableAST*>(ExprAST_from_pb(& fr.var())),
      ExprAST_from_pb(& fr.start()),
      ExprAST_from_pb(& fr.end()),
      ExprAST_from_pb(& fr.body()),
      ExprAST_from_pb(& fr.incr()),
      range);
}

ExprAST* parseIf(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_if_()) return NULL;

  const pb::If& i = e.if_();

  return new IfExprAST(
      ExprAST_from_pb(& i.test_expr()),
      ExprAST_from_pb(& i.then_expr()),
      ExprAST_from_pb(& i.else_expr()), range);
}

ExprAST* parseInt(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_int_()) return NULL;

  const pb::Int& i = e.int_();
  string text = i.text();
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
  // parts
  // name
  // parent scope
  return NULL;
}

ExprAST* parseNil(const pb::Expr& e, const foster::SourceRange& range) {
  return new NilExprAST(range);
}

ExprAST* parseOp(const pb::Expr& e, const foster::SourceRange& range) {
  if (e.parts_size() == 1) {
    return new UnaryOpExprAST(e.name(),
                          ExprAST_from_pb(&e.parts(0)), range);
  } else if (e.parts_size() == 2) {
    return new BinaryOpExprAST(e.name(),
                           ExprAST_from_pb(&e.parts(0)),
                           ExprAST_from_pb(&e.parts(1)), range);
  } else {
    EDiag() << "protobuf Expr tagged OP (" << e.name() << ") with too many parts "
        << "(" << e.parts_size() << "): "
               << e.DebugString();
  }
  return NULL;
}

ExprAST* parseProto(const pb::Expr& e, const foster::SourceRange& range) {
  if (!e.has_proto()) return NULL;

  const pb::Proto& proto = e.proto();
  std::vector<VariableAST*> args;
  for (size_t i = 0; i < proto.in_args_size(); ++i) {
    ExprAST* arg = ExprAST_from_pb(& proto.in_args(i));
    args.push_back(dynamic_cast<VariableAST*>(arg));
  }

  TypeAST* retTy = NULL;
  if (proto.has_result()) {
    retTy = TypeAST_from_pb(& proto.result());
  }

  const std::string& name = proto.name();

  // TODO lexical scope?
  return new PrototypeAST(retTy, name, args, range);
}

ExprAST* parseRef(const pb::Expr& e, const foster::SourceRange& range) {
  bool isNullable = false;
  bool isIndirect = false;
  return new RefExprAST(ExprAST_from_pb(&e.parts(0)),
                        isNullable, isIndirect, range);
}

ExprAST* parseSeq(const pb::Expr& e, const foster::SourceRange& range) {
  Exprs args;
  for (size_t i = 0; i < e.parts_size(); ++i) {
    args.push_back(ExprAST_from_pb(&e.parts(i)));
  }
  return new SeqAST(args, range);
}

ExprAST* parseSimd(const pb::Expr& e, const foster::SourceRange& range) {
  return new SimdVectorAST(ExprAST_from_pb(& e.parts(0)), range);
}

ExprAST* parseSubscript(const pb::Expr& e, const foster::SourceRange& range) {
  return new SubscriptAST(
      ExprAST_from_pb(& e.parts(0)),
      ExprAST_from_pb(& e.parts(1)), range);
}

ExprAST* parseTuple(const pb::Expr& e, const foster::SourceRange& range) {
  TupleExprAST* rv = new TupleExprAST(ExprAST_from_pb(&e.parts(0)), range);
  rv->isClosureEnvironment = e.is_closure_environment();
  return rv;
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
  case pb::Expr::ASSIGN:    rv = parseAssign(e, range); break;
  case pb::Expr::BOOL:      rv = parseBool(e, range); break;
  case pb::Expr::CALL:      rv = parseCall(e, range); break;
  case pb::Expr::CLOSURE:   rv = parseClosure(e, range); break;
  case pb::Expr::COMPILES:  rv = parseCompiles(e, range); break;
  case pb::Expr::DEREF:     rv = parseDeref(e, range); break;
  case pb::Expr::FN:        rv = parseFn(e, range); break;
  case pb::Expr::FORRANGE:  rv = parseForrange(e, range); break;
  case pb::Expr::IF:        rv = parseIf(e, range); break;
  case pb::Expr::INT:       rv = parseInt(e, range); break;
  case pb::Expr::MODULE:    rv = parseModule(e, range); break;
  case pb::Expr::NIL:       rv = parseNil(e, range); break;
  case pb::Expr::OP:        rv = parseOp(e, range); break;
  case pb::Expr::PROTO:     rv = parseProto(e, range); break;
  case pb::Expr::REF:       rv = parseRef(e, range); break;
  case pb::Expr::SEQ:       rv = parseSeq(e, range); break;
  case pb::Expr::SIMD:      rv = parseSimd(e, range); break;
  case pb::Expr::SUBSCRIPT: rv = parseSubscript(e, range); break;
  case pb::Expr::TUPLE:     rv = parseTuple(e, range); break;
  case pb::Expr::VAR:       rv = parseVar(e, range); break;

  default:
    break;
  }

  if (!rv) {
    EDiag() << "Unable to reconstruct ExprAST from protobuf Expr:"
            << e.DebugString();
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

    TypeAST* retTy = TypeAST_from_pb(&fnty.ret_type());

    std::vector<TypeAST*> argTypes(fnty.arg_types_size());
    for (int i = 0; i < argTypes.size(); ++i) {
      argTypes[i] = TypeAST_from_pb(&fnty.arg_types(i));
    }

    std::string callingConvention = "fastcc";
    if (fnty.has_calling_convention()) {
      callingConvention = fnty.calling_convention();
      std::cout << "setting calling convention to " << callingConvention << std::endl;
    }

    return FnTypeAST::get(retTy, argTypes, callingConvention);
  }

  if (t.tuple_parts_size() > 0) {
    std::vector<TypeAST*> parts(t.tuple_parts_size());
    for (int i = 0; i < parts.size(); ++i) {
      parts[i] = TypeAST_from_pb(&t.tuple_parts(i));
    }
    return TupleTypeAST::get(parts);
  }

  if (t.has_closurety()) {
    const pb::ClosureType& cty = t.closurety();

    PrototypeAST* proto = NULL;
    TupleTypeAST* cloTupleType = NULL;
    FnTypeAST* cloFnType = NULL;
    const llvm::Type* underlyingType = NULL;

    if (cty.has_proto()) {
      proto = dynamic_cast<PrototypeAST*>(ExprAST_from_pb(&cty.proto()));
    }

    if (cty.has_fntype()) {
      cloFnType = dynamic_cast<FnTypeAST*>(TypeAST_from_pb(&cty.fntype()));
    }

    if (cty.has_clo_tuple_type()) {
      cloTupleType = dynamic_cast<TupleTypeAST*>(
                                     TypeAST_from_pb(&cty.clo_tuple_type()));
    }

    ASSERT(proto) << "Need a proto to reconstruct a closure type." << show(range);
    ClosureTypeAST* ct = new ClosureTypeAST(proto, underlyingType, range);
    ct->fntype = cloFnType;
    ct->clotype = cloTupleType;
    return ct;
  }

  if (t.has_literal_int_value()) {
    return LiteralIntValueTypeAST::get(t.literal_int_value(), range);
  }

  if (t.has_simd_vector()) {
    const pb::SimdVectorType& st = t.simd_vector();
    TypeAST* literalIntSize = TypeAST_from_pb(&st.literal_int_size());
    TypeAST* elementType    = TypeAST_from_pb(&st.element_type());
    return SimdVectorTypeAST::get(
        dynamic_cast<LiteralIntValueTypeAST*>(literalIntSize),
        elementType, range);
  }

  if (t.tag() == pb::Type::LLVM_NAMED) {
    const string& tyname = t.llvm_type_name();
    std::cerr << "PB trying to reconstruct named type: '" << tyname << "'" << std::endl;

    ASSERT(!tyname.empty()) << "empty type name, probably implies a\n"
                  << "missing pb.if_X() check before pb.X().\n"
                  << "Use gdb to find the culprit.";

    TypeAST* rv = NULL;
    if (!tyname.empty() && tyname != "<NULL Ty>") {
      rv = foster::TypeASTFor(tyname);
    }
    return rv;
  }

  std::cerr << "Error: found unexpected type in protobuf!\n" << t.DebugString() << std::endl;

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
