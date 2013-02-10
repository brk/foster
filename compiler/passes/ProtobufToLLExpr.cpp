// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/SourceRange.h"
#include "base/LLVMUtils.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/ParsingContext.h"
#include "parse/FosterTypeAST.h"
#include "parse/ProtobufToLLExpr.h"

#include "passes/FosterLL.h"

#include <sstream>

#include "_generated_/FosterIL.pb.h"

#include <vector>

struct LLExpr;

namespace foster {

namespace bepb {
  struct Expr;
  struct Type;
} // namespace foster::bepb

LLExpr* LLExpr_from_pb(const bepb::Letable*);
TypeAST* TypeAST_from_pb(const bepb::Type*);
FnTypeAST* parseProcType(const bepb::ProcType&);
}

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

CtorInfo parseCtorInfo(const pb::PbCtorInfo& c) { CtorInfo x;
  x.ctorId = parseCtorId(c.ctor_id());
  x.ctorStructType = NULL;
  if (c.has_ctor_struct_ty()) {
    x.ctorStructType = const_cast<StructTypeAST*>(
                         TypeAST_from_pb(&c.ctor_struct_ty())
                                           ->castStructTypeAST());
    ASSERT(x.ctorStructType != NULL);
  }
  return x;
}

LLExpr* parseBool(const pb::Letable& e) {
  return new LLBool(e.bool_value() ? "true" : "false");
}

LLExpr* parseText(const pb::Letable& e) {
  return new LLText(e.string_value());
}

LLVar* parseTermVar(const pb::TermVar& v) {
  ASSERT(v.name() != "") << "parseTermVar got empty var!";
  LLVar* rv = NULL;

  switch (v.tag()) {
  case pb::TermVar::IL_VAR:           rv = new          LLVar(v.name()); break;
  case pb::TermVar::IL_GLOBAL_SYMBOL: rv = new LLGlobalSymbol(v.name()); break;
  }
  ASSERT(rv != NULL) << "parseTermVar didn't recognize tag.";
  if (v.has_typ()) {
    rv->type = TypeAST_from_pb(& v.typ());
  }
  return rv;
}

LLExpr* parseCoroPrim(const pb::PbCoroPrim& p) {
  TypeAST* r = TypeAST_from_pb(& p.ret_type());
  TypeAST* a = TypeAST_from_pb(& p.arg_type());
  switch (p.tag()) {
  case pb::PbCoroPrim::IL_CORO_INVOKE: return new LLCoroPrim("coro_invoke", r, a);
  case pb::PbCoroPrim::IL_CORO_CREATE: return new LLCoroPrim("coro_create", r, a);
  case pb::PbCoroPrim::IL_CORO_YIELD : return new LLCoroPrim("coro_yield",  r, a);
  default: ASSERT(false) << "unknown coro prim tag number " << p.tag();
           return NULL;
  }
}

LLExpr* parseCall(const pb::Letable& e) {
  ASSERT(e.parts_size() >= 1);
  ASSERT(e.has_call_info());
  const pb::PbCallInfo& c = e.call_info();

  int firstArg = c.has_coro_prim() ? 0 : 1;
  LLExpr* base = c.has_coro_prim() ? parseCoroPrim(c.coro_prim())
                                   : parseTermVar(e.parts(0));
  std::vector<LLVar*> args;
  for (int i = firstArg; i < e.parts_size(); ++i) {
    args.push_back(parseTermVar(e.parts(i)));
  }
  return new LLCall(base, args, c.call_may_trigger_gc(),
                    c.call_is_a_tail_call(), c.call_conv());
}

LLExpr* parseCallPrimOp(const pb::Letable& e) {
  ASSERT(e.parts_size() >= 1);
  std::vector<LLVar*> args;
  for (int i = 0; i < e.parts_size(); ++i) {
    args.push_back(parseTermVar(e.parts(i)));
  }
  return new LLCallPrimOp(e.prim_op_name(), args);
}

LLExpr* parseInt(const pb::Letable& e) {
  if (!e.has_pb_int()) return NULL;
  const pb::PBInt& i = e.pb_int();
  return new LLInt(i.clean(), i.bits());
}

LLExpr* parseFloat(const pb::Letable& e) {
  return new LLFloat(e.dval());
}

LLAllocate::MemRegion parseMemRegion(const pb::PbAllocInfo& a) {
  LLAllocate::MemRegion target_region = LLAllocate::MEM_REGION_STACK;
  switch (a.mem_region()) {
  case           pb::PbAllocInfo::MEM_REGION_STACK:
      target_region = LLAllocate::MEM_REGION_STACK; break;
  case           pb::PbAllocInfo::MEM_REGION_GLOBAL_HEAP:
      target_region = LLAllocate::MEM_REGION_GLOBAL_HEAP; break;
  default: ASSERT(false) << "Unknown target region for AllocInfo.";
  }
  return target_region;
}

LLAllocate* parseAllocInfo(const pb::PbAllocInfo& a) {
  LLVar* array_size = NULL;
  if (a.has_array_size()) {
    array_size = parseTermVar(a.array_size());
  }

  std::string tynm = a.type_name();
  LLAllocate::MemRegion target_region = parseMemRegion(a);
  int8_t bogusCtorTag = -2;
  int8_t ctorTag = a.has_ctor_tag() ? a.ctor_tag() : bogusCtorTag;
  return new LLAllocate(TypeAST_from_pb(& a.type()), tynm, ctorTag,
                        array_size, target_region, a.alloc_site(),
                        a.zero_init());
}

LLAllocate* parseAllocate(const pb::Letable& e) {
  ASSERT(e.has_alloc_info());
  return parseAllocInfo(e.alloc_info());
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

LLTupleStore* parseTupleStore(const pb::TupleStore& ts) {
  std::vector<LLVar*> vars;
  for (int i = 0; i < ts.stored_vars_size(); ++i) {
    vars.push_back(parseTermVar(ts.stored_vars(i)));
  }
  return new LLTupleStore(vars, parseTermVar(ts.storage()), ts.storage_indir());
}

LLMiddle* parseLetVal(const pb::LetVal& b) {
  std::vector<std::string> names;
  std::vector<LLExpr*>     exprs;
  names.push_back(b.let_val_id());
  exprs.push_back(LLExpr_from_pb(&b.let_expr()));
  return new LLLetVals(names, exprs);
}

LLExpr* parseBitcast(const pb::Letable& e) {
  ASSERT(e.parts_size() == 1) << "bitcast muse have var to cast";
  return new LLBitcast(parseTermVar(e.parts(0)));
}

LLMiddle* parseGCRootInit(const pb::RootInit& r) {
  return new LLGCRootInit(parseTermVar(r.root_init_src()),
                          parseTermVar(r.root_init_root()));
}

LLMiddle* parseGCRootKill(const pb::RootKill& r) {
  return new LLGCRootKill(parseTermVar(r.root_kill_root()),
                          r.root_kill_null());
}

LLMiddle* parseRebindId(const pb::RebindId& r) {
  return new LLRebindId(r.from_id(), parseTermVar(r.to_var()));
}

LLSwitch* parseSwitch(const pb::Terminator&);

LLBr* parseBr(const pb::Terminator& b) {
  std::vector<LLVar*> args;
  for (int i = 0; i < b.args_size(); ++i) {
      args.push_back(parseTermVar(b.args(i)));
  }
  return new LLBr(b.block(), args);
}

LLTerminator* parseTerminator(const pb::Terminator& b) {
  LLTerminator* rv = NULL;
  switch (b.tag()) {
  case pb::Terminator::BLOCK_RET_VOID: return new LLRetVoid();
  case pb::Terminator::BLOCK_RET_VAL: return new LLRetVal(parseTermVar(b.var()));
  case pb::Terminator::BLOCK_BR: return parseBr(b);
  case pb::Terminator::BLOCK_CASE: return parseSwitch(b);
  default: ASSERT(false); return NULL;
  }
  return rv;
}


LLMiddle* parseMiddle(const pb::BlockMiddle& b) {
  if (b.has_tuple_store()) { return parseTupleStore(b.tuple_store()); }
  if (b.has_let_val()) { return parseLetVal(b.let_val()); }
  if (b.has_rebind())  { return parseRebindId(b.rebind()); }
  if (b.has_gcroot_kill()) { return parseGCRootKill(b.gcroot_kill()); }
  if (b.has_gcroot_init()) { return parseGCRootInit(b.gcroot_init()); }
  ASSERT(false) << "parseMiddle unhandled case!"; return NULL;
}

LLBlock* parseBlock(const pb::Block& b) {
  LLBlock* bb = new LLBlock;
  bb->block_id = b.block_id();
  bb->numPreds = b.has_num_preds() ? b.num_preds() : 0;
  for (int i = 0; i < b.middle_size(); ++i) {
    bb->mids.push_back(parseMiddle(b.middle(i)));
  }
  for (int i = 0; i < b.phis_size(); ++i) {
    bb->phiVars.push_back(parseTermVar(b.phis(i)));
  }
  bb->terminator = parseTerminator(b.last());
  return bb;
}

LLProc* parseProc(const pb::Proc& e) {
  ASSERT(e.has_proctype()) << "protobuf LLProc missing proc type!";

  FnTypeAST* proctype = parseProcType(e.proctype());

  std::vector<std::string> args;
  for (int i = 0; i < e.in_args_size(); ++i) {
    args.push_back(e.in_args(i));
  }

  std::vector<LLBlock*> blocks;
  for (int i = 0; i < e.blocks_size(); ++i) {
    blocks.push_back(parseBlock(e.blocks(i)));
  }

  std::vector<LLVar*> gcroots;
  for (int i = 0; i < e.gcroots_size(); ++i) {
    gcroots.push_back(parseTermVar(e.gcroots(i)));
  }

  foster::sgProcLines[e.name()] = e.lines();

  return new LLProcCFG(proctype, e.name(), args,
                       parseLinkage(e.linkage()),
                       blocks, gcroots);
}

LLArrayIndex* parseArrayIndex(const pb::Letable& e) {
  ASSERT(e.parts_size() >= 2) << "array_index must have base and index";
  return new LLArrayIndex(parseTermVar( e.parts(0)),
                          parseTermVar( e.parts(1)),
                          e.string_value(),
                          e.prim_op_name());
}

LLExpr* parseArrayRead(const pb::Letable& e) {
  ASSERT(e.parts_size() == 2) << "array_read must have base and index";
  return new LLArrayRead(parseArrayIndex(e));
}

LLExpr* parseArrayPoke(const pb::Letable& e) {
  ASSERT(e.parts_size() == 3) << "array_write must have value, base and index";
  return new LLArrayPoke(parseArrayIndex(e),
                         parseTermVar( e.parts(2)));
}

LLExpr* parseArrayLength(const pb::Letable& e) {
  ASSERT(e.parts_size() == 1) << "array_length must have value";
  return new LLArrayLength(parseTermVar( e.parts(0)));
}

LLOccurrence* parseOccurrence(const pb::PbOccurrence& o) {
  LLOccurrence* rv = new LLOccurrence;
  for (int i = 0; i < o.occ_offset_size(); ++i) {
    rv->offsets.push_back(o.occ_offset(i));
  }
  for (int i = 0; i < o.occ_ctors_size(); ++i) {
    rv->ctors.push_back(parseCtorInfo(o.occ_ctors(i)));
  }
  rv->var = parseTermVar(o.scrutinee());
  if (o.has_type()) {
    rv->type = TypeAST_from_pb(& o.type());
  }
  return rv;
}

LLSwitch* parseSwitch(const pb::Terminator& b) {
  const pb::PbSwitch& sc = b.scase();

  std::vector<CtorId> ctors;
  for (int i = 0; i < sc.ctors_size(); ++i) {
    ctors.push_back(parseCtorId(sc.ctors(i)));
  }

  std::vector<std::string> ids;
  for (int i = 0; i < sc.blocks_size(); ++i) {
    ids.push_back(sc.blocks(i));
  }

  std::string def;
  if (sc.has_defcase()) { def = sc.defcase(); }

  return new LLSwitch(
      parseOccurrence(sc.occ()),
      ctors, ids, def);
}

LLExpr* parseDeref(const pb::Letable& e) {
  return new LLDeref(parseTermVar( e.parts(0)));
}

LLExpr* parseStore(const pb::Letable& e) {
  return new LLStore(
      parseTermVar( e.parts(0)),
      parseTermVar( e.parts(1)));
}

LLExpr* parseObjectCopy(const pb::Letable& e) {
  return new LLObjectCopy(
      parseTermVar( e.parts(0)),
      parseTermVar( e.parts(1)));
}

LLExpr* parseKillProcess(const pb::Letable& e) {
  return new LLKillProcess(e.string_value());
}

LLExpr* parseUnitValue(const pb::Letable& e) { return new LLUnitValue(); }

} // unnamed namespace

////////////////////////////////////////////////////////////////////

LLDecl* parseDecl(const pb::Decl& e) {
  return new LLDecl(      e.name(),
        TypeAST_from_pb(& e.type()));
}

LLModule* LLModule_from_pb(const pb::Module& e) {
  string moduleName = e.modulename();

  // Walk the type declarations and add their types to the current scope.
  // In contrast, the extern value declarations are only for checking purposes;
  // if a value isn't in a Module we've imported, we can't magically summon it!
  std::vector<NamedTypeAST*> namedTypes;
  for (int i = 0; i < e.typ_decls_size(); ++i){
    namedTypes.push_back(new NamedTypeAST(e.typ_decls(i).name(), NULL,
                         foster::SourceRange::getEmptyRange()));
    ParsingContext::insertType(e.typ_decls(i).name(),
                               namedTypes.back());
  }
  // We use an indirection through NamedTypeAST to break cyclic references.
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

  std::vector<LLDecl*> evdecls;
  for (int i = 0; i < e.extern_val_decls_size(); ++i) {
    evdecls.push_back(parseDecl(e.extern_val_decls(i)));
  }

  return new LLModule(moduleName, procs, evdecls, datatype_decls);
}


LLExpr* LLExpr_from_pb(const pb::Letable* pe) {
  if (!pe) return NULL;
  const pb::Letable& e = *pe;

  LLExpr* rv = NULL;

  switch (e.tag()) {
  case pb::Letable::IL_BOOL:        rv = parseBool(e); break;
  case pb::Letable::IL_CALL:        rv = parseCall(e); break;
  case pb::Letable::IL_CALL_PRIMOP: rv = parseCallPrimOp(e); break;
  case pb::Letable::IL_INT:         rv = parseInt(e); break;
  case pb::Letable::IL_FLOAT:       rv = parseFloat(e); break;
  case pb::Letable::IL_TEXT:        rv = parseText(e); break;
  case pb::Letable::IL_UNIT:        rv = parseUnitValue(e); break;
  case pb::Letable::IL_DEREF:       rv = parseDeref(e); break;
  case pb::Letable::IL_STORE:       rv = parseStore(e); break;
  case pb::Letable::IL_BITCAST:     rv = parseBitcast(e); break;
  case pb::Letable::IL_ARRAY_READ:  rv = parseArrayRead(e); break;
  case pb::Letable::IL_ARRAY_POKE:  rv = parseArrayPoke(e); break;
  case pb::Letable::IL_ARRAY_LENGTH:rv = parseArrayLength(e); break;
  case pb::Letable::IL_ALLOCATE:    rv = parseAllocate(e); break;
  case pb::Letable::IL_OCCURRENCE:  rv = parseOccurrence(e.occ()); break;
  case pb::Letable::IL_OBJECT_COPY: rv = parseObjectCopy(e); break;
  case pb::Letable::IL_KILL_PROCESS:rv = parseKillProcess(e); break;

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

////////////////////////////////////////////////////////////////////

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
    ASSERT(t.type_parts_size() == 1);
    return ArrayTypeAST::get(TypeAST_from_pb(&t.type_parts(0)));
  }

  if (t.tag() == pb::Type::PTR) {
    ASSERT(t.type_parts_size() == 1);
    return RefTypeAST::get(TypeAST_from_pb(&t.type_parts(0)));
  }

  if (t.tag() == pb::Type::PROC) {
    return parseProcType(t.procty());
  }

  if (t.tag() == pb::Type::STRUCT) {
    std::vector<TypeAST*> parts(t.type_parts_size());
    for (size_t i = 0; i < parts.size(); ++i) {
      parts[i] = TypeAST_from_pb(&t.type_parts(i));
    }
    return StructTypeAST::get(parts);
  }

  if (t.tag() == pb::Type::CORO) {
    ASSERT(t.type_parts_size() == 2)
        << "coro must have base and arg types,"
        << " but #type parts is " << t.type_parts_size();
    TypeAST* targ = TypeAST_from_pb(&t.type_parts(0));
    TypeAST* tret = TypeAST_from_pb(&t.type_parts(1));
    return CoroTypeAST::get(targ, tret);
  }

  if (t.tag() == pb::Type::NAMED) {
    const string& tyname = t.name();

    ASSERT(!tyname.empty()) << "empty type name, probably implies a\n"
                  << "missing pb.if_X() check before pb.X().\n"
                  << "Use gdb to find the culprit.";

    TypeAST* rv = NULL;
    if (!tyname.empty() && tyname != "<NULL Ty>") {
      rv = foster::ParsingContext::lookupType(tyname);
    }
    ASSERT(rv) << "unable to find type named " << tyname;
    return rv;
  }

  if (t.tag() == pb::Type::PRIM_INT) {
    int size = t.carray_size();

    llvm::Type* ty;
    // -32 means word size; -64 means 2x word.
    std::stringstream name;
    if (size == -32) {
      name << "Word";
      ty = getWordTy(builder);
    } else if (size == -64) {
      name << "WordX2";
      ty = getWordX2Ty(builder);
    } else {

      ty = llvm::IntegerType::get(llvm::getGlobalContext(), size);
      if (size == 1) {
        name << "Bool";
      } else if (size > 0) {
        name << "Int" << size;
      }
    }
    return PrimitiveTypeAST::get(name.str(), ty);
  }

  if (t.tag() == pb::Type::FLOAT64) {
    return PrimitiveTypeAST::get("Float64",
                             llvm::Type::getDoubleTy(llvm::getGlobalContext()));
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

