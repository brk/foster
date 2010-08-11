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

ExprAST* ExprAST_from_pb(const pb::Expr* pe) {
  if (!pe) return NULL;
  const pb::Expr& e = *pe;

  foster::SourceRange range = foster::SourceRange::getEmptyRange();
  if (e.has_range()) {
    parseRangeFrom(range, e);
  }

  /*
  switch (e.tag()) {
  case pb::Expr::ASSIGN:
    break;
  default:
    break;
  }
  */

  if (e.has_bool_value()) {
    return new BoolAST(e.bool_value() ? "true" : "false", range);
  }

  if (e.has_int_()) {
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

  if (e.tag() == pb::Expr::VAR) {
    return new VariableAST(e.name(), TypeAST_from_pb(&e.type()), range);
  }

  if (e.tag() == pb::Expr::OP) {
    if (e.parts_size() == 1) {
      return new UnaryOpExprAST(e.name(),
                            ExprAST_from_pb(&e.parts(0)), range);
    } else if (e.parts_size() == 2) {
      return new BinaryOpExprAST(e.name(),
                             ExprAST_from_pb(&e.parts(0)),
                             ExprAST_from_pb(&e.parts(1)), range);
    } else {
      EDiag() << "protobuf Expr tagged OP with too many parts: "
              << e.DebugString();
    }
  }

  return NULL;
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
    const pb::Expr& eproto = cty.proto();
    const pb::Type& fntype = cty.fntype();
    const pb::Type& clo_tuple_type = cty.clo_tuple_type();

    return NULL;
#if 0
    return new ClosureTypeAST(
        dynamic_cast<PrototypeAST*>(ExprAST_from_pb(eproto)),
        ,
        range);
#endif
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
    std::cerr << "PB trying to reconstruct named type: " << t.llvm_type_name() << std::endl;
    TypeAST* rv = foster::TypeASTFor(t.llvm_type_name());
    std::cerr << "..." << std::endl;
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
