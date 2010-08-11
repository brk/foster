// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

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

void initSourceLocation(foster::SourceLocation& loc, foster::pb::SourceLocation* pbloc);

template <typename PB>
void parseRangeFrom(foster::SourceRange& r, PB& p) {
  foster::pb::SourceRange* sr = p.mutable_range();
  initSourceLocation(const_cast<foster::SourceLocation&>(r.begin), sr->mutable_begin());
  initSourceLocation(const_cast<foster::SourceLocation&>(r.end  ), sr->mutable_end());

  r.source = NULL;

  if (sr->has_file_path()) {
    const std::string& pathstr = sr->file_path();
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

ExprAST* ExprAST_from_pb(pb::Expr* pe) {
  if (!pe) return NULL;
  pb::Expr& e = *pe;

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
    pb::Int* i = e.mutable_int_();
    string text = i->text();
    string clean = pystring::replace(text, "`", "");
    vector<string> parts;
    pystring::split(clean, parts, "_");
    int base = 10;
    if (parts.size() == 2) {
      clean = parts[0];
      std::stringstream ss; ss << parts[1]; ss >> base;
    }

    return foster::parseInt(clean, i->text(), base, range);
  }

  return NULL;
}

TypeAST* TypeAST_from_pb(pb::Type* pt) {
  if (!pt) return NULL;
  pb::Type& t = *pt;

  foster::SourceRange range = foster::SourceRange::getEmptyRange();
  if (t.has_range()) {
    parseRangeFrom(range, t);
  }

  if (t.has_ref_underlying_type()) {
    TypeAST* baseType = TypeAST_from_pb(t.mutable_ref_underlying_type());
    return RefTypeAST::get(baseType);
  }

  if (t.has_fnty()) {
    foster::pb::FnType* fnty = t.mutable_fnty();

    TypeAST* retTy = TypeAST_from_pb(fnty->mutable_ret_type());

    std::vector<TypeAST*> argTypes(fnty->arg_types_size());
    for (int i = 0; i < argTypes.size(); ++i) {
      pb::Type argTy = fnty->arg_types(i);
      argTypes[i] = TypeAST_from_pb(&argTy);
    }

    std::string callingConvention = "fastcc";
    if (fnty->has_calling_convention()) {
      callingConvention = fnty->calling_convention();
      std::cout << "setting calling convention to " << callingConvention << std::endl;
    }

    return FnTypeAST::get(retTy, argTypes, callingConvention);
  }

  if (t.tuple_parts_size() > 0) {
    std::vector<TypeAST*> parts(t.tuple_parts_size());
    for (int i = 0; i < parts.size(); ++i) {
      pb::Type tt = t.tuple_parts(i);
      parts[i] = TypeAST_from_pb(&tt);
    }
    return TupleTypeAST::get(parts);
  }

  if (t.has_closurety()) {
    pb::ClosureType* cty = t.mutable_closurety();
    pb::Expr* eproto = cty->mutable_proto();
    pb::Type* fntype = cty->mutable_fntype();
    pb::Type* clo_tuple_type = cty->mutable_clo_tuple_type();

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
    pb::SimdVectorType* st = t.mutable_simd_vector();
    TypeAST* literalIntSize = TypeAST_from_pb(st->mutable_literal_int_size());
    TypeAST* elementType    = TypeAST_from_pb(st->mutable_element_type());
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


void initSourceLocation(foster::SourceLocation& loc, foster::pb::SourceLocation* pbloc) {
  if (!pbloc) {
    loc = foster::SourceLocation::getInvalidLocation();
  } else {
    loc.line = pbloc->line();
    loc.column = pbloc->column();
  }
}
