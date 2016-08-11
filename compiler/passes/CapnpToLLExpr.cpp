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

#include "_generated_/FosterIL.capnp.h"

#include <vector>

struct LLExpr;

namespace foster {

namespace be {
  struct Expr;
  struct Type;
}

LLExpr* LLExpr_from_pb(const be::Letable::Reader&);
TypeAST* TypeAST_from_pb(const be::Type::Reader&);
FnTypeAST* parseProcType(const be::ProcType::Reader&);
}

using std::string;
using std::vector;

namespace pb = foster::be;

namespace foster {

// In LLVMUtils.cpp
extern std::map<std::string, std::string> sgProcLines;

namespace {

CtorRepr parseCtorRepr(const pb::PbCtorRepr::Reader& c) { CtorRepr x;
  bool isUnboxed  = c.hasIsboxed() && (c.getIsboxed().size() == 1) && !c.getIsboxed()[0];
  x.isTransparent = c.getTag() == pb::PbCtorRepr::Tag::CRTRANSPARENT;
  x.isNullary     = c.getTag() == pb::PbCtorRepr::Tag::CRNULLARY;
  x.isBoxed       = !isUnboxed;
  x.smallId       = int64_t(c.getCtorreprtag()[0]);
  return x;
}

CtorId parseCtorId(const pb::PbCtorId::Reader& c) { CtorId x;
  x.typeName = c.getCtortypename();
  x.ctorName = c.getCtorctorname();
  x.ctorRepr = parseCtorRepr(c.getCtorrepr());
  //DDiag() << "parsed ctor " << x.typeName               << "." << x.ctorName
  //        << " ; repr "     << x.ctorRepr.isTransparent << ";"
  //                          << x.ctorRepr.isNullary     << ";" << x.ctorRepr.smallId
  //        << " ; tag = " << c.ctor_repr().tag() ;
  return x;
}

CtorInfo parseCtorInfo(const pb::PbCtorInfo::Reader& c) { CtorInfo x;
  x.ctorId = parseCtorId(c.getCtorid());
  x.ctorStructType = NULL;
  if (c.hasCtorstructty()) {
    x.ctorStructType = const_cast<StructTypeAST*>(
                         TypeAST_from_pb(c.getCtorstructty())
                                           ->castStructTypeAST());
    ASSERT(x.ctorStructType != NULL);
  }
  return x;
}

LLExpr* parseBool(const pb::Letable::Reader& e) {
  auto bools = e.getBoolvalue();
  return new LLBool( (bools.size() > 0 && bools[0]) ? "true" : "false");
}

LLExpr* parseText(const pb::Letable::Reader& e) {
  return new LLText(e.getStringvalue());
}

LLVar* parseTermVar(const pb::TermVar::Reader& v) {
  ASSERT(v.getName() != "") << "parseTermVar got empty var!";
  LLVar* rv = NULL;

  switch (v.getTag()) {
  case pb::TermVar::Tag::ILVAR:          rv = new          LLVar(v.getName()); break;
  case pb::TermVar::Tag::ILGLOBALSYMBOL: rv = new LLGlobalSymbol(v.getName()); break;
  }
  ASSERT(rv != NULL) << "parseTermVar didn't recognize tag.";
  if (v.hasTyp()) {
    rv->type = TypeAST_from_pb(v.getTyp());
  }
  return rv;
}

LLExpr* parseCoroPrim(const pb::PbCoroPrim::Reader& p) {
  TypeAST* r = TypeAST_from_pb(p.getRettype());
  TypeAST* a = TypeAST_from_pb(p.getArgtype());
  switch (p.getTag()) {
  case pb::PbCoroPrim::Tag::ILCOROINVOKE: return new LLCoroPrim("coro_invoke", r, a);
  case pb::PbCoroPrim::Tag::ILCOROCREATE: return new LLCoroPrim("coro_create", r, a);
  case pb::PbCoroPrim::Tag::ILCOROYIELD : return new LLCoroPrim("coro_yield",  r, a);
  }
  ASSERT(false) << "unknown coro prim tag number " << int(p.getTag());
  return NULL;
}

LLExpr* parseCallAsm(const pb::Letable::Reader& e) {
  const pb::PbCallAsm::Reader& c = e.getCallasm();

  std::vector<LLVar*> args;
  for (auto p : e.getParts()) {
    args.push_back(parseTermVar(p));
  }
  FnTypeAST* ty = parseProcType(c.getAsmproctype());
  return new LLCallInlineAsm(ty, c.getAsmcontents(),
               c.getConstraints(), c.getHassideeffects(), args);
}

LLExpr* parseCall(const pb::Letable::Reader& e) {
  if (e.hasCallasm()) return parseCallAsm(e);

  ASSERT(e.getParts().size() >= 1);
  ASSERT(e.hasCallinfo());
  const pb::PbCallInfo::Reader& c = e.getCallinfo();

  unsigned firstArg = c.hasCoroprim() ? 0 : 1;
  LLExpr* base = c.hasCoroprim() ? parseCoroPrim(c.getCoroprim())
                                 : parseTermVar(e.getParts()[0]);
  std::vector<LLVar*> args;
  for (unsigned i = firstArg; i < e.getParts().size(); ++i) {
    args.push_back(parseTermVar(e.getParts()[i]));
  }
  return new LLCall(base, args, c.getCallmaytriggergc(),
                    c.getCallisatailcall(), c.getCallconv());
}

LLExpr* parseCallPrimOp(const pb::Letable::Reader& e) {
  ASSERT(e.getParts().size() >= 1);
  std::vector<LLVar*> args;
  for (auto p : e.getParts()) {
    args.push_back(parseTermVar(p));
  }
  return new LLCallPrimOp(e.getPrimopname(), args);
}

LLExpr* parsePbInt(const pb::PBInt::Reader& i) {
  return new LLInt(i.getClean(), i.getBits());
}

LLExpr* parseInt(const pb::Letable::Reader& e) {
  ASSERT(e.hasPbint());
  return parsePbInt(e.getPbint());
}

LLExpr* parseFloat(const pb::Letable::Reader& e) {
  return new LLFloat(e.getDval()[0]);
}

LLAllocate::MemRegion parseMemRegion(const pb::PbAllocInfo::Reader& a) {
  LLAllocate::MemRegion target_region = LLAllocate::MEM_REGION_STACK;
  switch (a.getMemregion()) {
  case pb::PbAllocInfo::MemRegion::MEMREGIONSTACK:
       target_region = LLAllocate::MEM_REGION_STACK; break;
  case pb::PbAllocInfo::MemRegion::MEMREGIONGLOBALHEAP:
       target_region = LLAllocate::MEM_REGION_GLOBAL_HEAP; break;
  case pb::PbAllocInfo::MemRegion::MEMREGIONGLOBALDATA:
       target_region = LLAllocate::MEM_REGION_GLOBAL_DATA; break;
  }
  if (target_region == LLAllocate::MEM_REGION_STACK
   && a.getMemregion() != pb::PbAllocInfo::MemRegion::MEMREGIONSTACK) {
    ASSERT(false) << "Unknown target region for AllocInfo.";
  }
  return target_region;
}

LLAllocate* parseAllocInfo(const pb::PbAllocInfo::Reader& a) {
  LLVar* array_size = NULL;
  if (a.hasArraysize()) {
    array_size = parseTermVar(a.getArraysize());
  }

  std::string tynm = a.getTypename();
  LLAllocate::MemRegion target_region = parseMemRegion(a);
  CtorRepr ctorRepr;
  if (a.hasCtorrepr()) {
    ctorRepr = parseCtorRepr(a.getCtorrepr());
  } else {
    int bogusCtorTag = -2;
    ctorRepr.smallId       = bogusCtorTag;
    ctorRepr.isTransparent = false;
  }
  return new LLAllocate(TypeAST_from_pb(a.getType()), tynm, ctorRepr,
                        array_size, target_region, a.getAllocsite(),
                        a.getZeroinit());
}

LLAllocate* parseAllocate(const pb::Letable::Reader& e) {
  ASSERT(e.hasAllocinfo());
  return parseAllocInfo(e.getAllocinfo());
}

llvm::GlobalValue::LinkageTypes
parseLinkage(const pb::Proc::Linkage linkage) {
  switch (linkage) {
  case pb::Proc::Linkage::INTERNAL: return llvm::GlobalValue::InternalLinkage;
  case pb::Proc::Linkage::EXTERNAL: return llvm::GlobalValue::ExternalLinkage;
  }
  ASSERT(false) << "unknown linkage!";
  return llvm::GlobalValue::InternalLinkage;
}

LLTupleStore* parseTupleStore(const pb::TupleStore::Reader& ts) {
  std::vector<LLVar*> vars;
  for (auto sv : ts.getStoredvars()) {
    vars.push_back(parseTermVar(sv));
  }
  return new LLTupleStore(vars, parseTermVar(ts.getStorage()), ts.getStorageindir());
}

LLMiddle* parseLetVal(const pb::LetVal::Reader& b) {
  std::vector<std::string> names;
  std::vector<LLExpr*>     exprs;
  names.push_back(b.getLetvalid());
  exprs.push_back(LLExpr_from_pb(b.getLetexpr()));
  return new LLLetVals(names, exprs);
}

LLExpr* parseBitcast(const pb::Letable::Reader& e) {
  ASSERT(e.getParts().size() == 1) << "bitcast muse have var to cast";
  return new LLBitcast(parseTermVar(e.getParts()[0]));
}

LLMiddle* parseGCRootInit(const pb::RootInit::Reader& r) {
  return new LLGCRootInit(parseTermVar(r.getRootinitsrc()),
                          parseTermVar(r.getRootinitroot()));
}

LLMiddle* parseGCRootKill(const pb::RootKill::Reader& r) {
  return new LLGCRootKill(parseTermVar(r.getRootkillroot()),
                          r.getRootkillnull());
}

LLMiddle* parseRebindId(const pb::RebindId::Reader& r) {
  return new LLRebindId(r.getFromid(), parseTermVar(r.getTovar()));
}

LLSwitch* parseSwitch(const pb::Terminator::Reader&);

LLBr* parseBr(const pb::Terminator::Reader& b) {
  std::vector<LLVar*> args;
  for (auto arg : b.getArgs()) {
      args.push_back(parseTermVar(arg));
  }
  return new LLBr(b.getBlock(), args);
}

LLTerminator* parseTerminator(const pb::Terminator::Reader& b) {
  switch (b.getTag()) {
  case pb::Terminator::Tag::BLOCKRETVOID: return new LLRetVoid();
  case pb::Terminator::Tag::BLOCKRETVAL: return new LLRetVal(parseTermVar(b.getVar()));
  case pb::Terminator::Tag::BLOCKBR: return parseBr(b);
  case pb::Terminator::Tag::BLOCKCASE: return parseSwitch(b);
  }
  ASSERT(false) << "Unknown terminator tag: " << int(b.getTag()) << "\n"; return NULL;
}


LLMiddle* parseMiddle(const pb::BlockMiddle::Reader& b) {
  if (b.hasTuplestore()) { return parseTupleStore(b.getTuplestore()); }
  if (b.hasLetval()) { return parseLetVal(b.getLetval()); }
  if (b.hasRebind())  { return parseRebindId(b.getRebind()); }
  if (b.hasGcrootkill()) { return parseGCRootKill(b.getGcrootkill()); }
  if (b.hasGcrootinit()) { return parseGCRootInit(b.getGcrootinit()); }
  ASSERT(false) << "parseMiddle unhandled case!"; return NULL;
}

LLBlock* parseBlock(const pb::Block::Reader& b) {
  LLBlock* bb = new LLBlock;
  bb->block_id = b.getBlockid();
  bb->numPreds = (b.hasNumpreds() && b.getNumpreds().size() > 0) ?
                                     b.getNumpreds()[0] : 0;
  for (auto middle : b.getMiddle()) {
    bb->mids.push_back(parseMiddle(middle));
  }
  for (auto phi : b.getPhis()) {
    bb->phiVars.push_back(parseTermVar(phi));
  }
  bb->terminator = parseTerminator(b.getLast());
  return bb;
}

LLProc* parseProc(const pb::Proc::Reader& e) {
  ASSERT(e.hasProctype()) << "protobuf LLProc missing proc type!";
  auto pt = e.getProctype();
  FnTypeAST* proctype = parseProcType(pt);

  std::vector<std::string> args;
  for (auto arg : e.getInargs()) {
    args.push_back(arg);
  }
  std::vector<LLBlock*> blocks;
  for (auto b : e.getBlocks()) {
    blocks.push_back(parseBlock(b));
  }

  std::vector<LLVar*> gcroots;
  for (auto r : e.getGcroots()) {
    gcroots.push_back(parseTermVar(r));
  }

  foster::sgProcLines[e.getName()] = e.getLines();
  return new LLProcCFG(proctype, e.getName(), args,
                       parseLinkage(e.getLinkage()),
                       blocks, gcroots);
}

LLArrayIndex* parseArrayIndex(const pb::Letable::Reader& e) {
  ASSERT(e.getParts().size() >= 2) << "array_index must have base and index";
  return new LLArrayIndex(parseTermVar( e.getParts()[0]),
                          parseTermVar( e.getParts()[1]),
                          e.getStringvalue(),
                          e.getPrimopname());
}

LLExpr* parseArrayRead(const pb::Letable::Reader& e) {
  ASSERT(e.getParts().size() == 2) << "array_read must have base and index";
  return new LLArrayRead(parseArrayIndex(e));
}

LLExpr* parseArrayPoke(const pb::Letable::Reader& e) {
  ASSERT(e.getParts().size() == 3) << "array_write must have value, base and index";
  return new LLArrayPoke(parseArrayIndex(e),
                         parseTermVar( e.getParts()[2]));
}

LLExpr* parseArrayLength(const pb::Letable::Reader& e) {
  ASSERT(e.getParts().size() == 1) << "array_length must have value";
  return new LLArrayLength(parseTermVar( e.getParts()[0]));
}

LLExpr* parseArrayEntry(const pb::PbArrayEntry::Reader& e) {
  ASSERT(e.hasVar() || e.hasLit());
  if (e.hasVar()) {
    return parseTermVar(e.getVar());
  }
  if (e.hasLit()) {
    return LLExpr_from_pb(e.getLit()); // TODO should eventually support float/bool too
  }
  ASSERT(false) << "parseArrayEntry requires a var or literal"; return NULL;
}

LLExpr* parseArrayLiteral(const pb::Letable::Reader& e) {
  ASSERT(e.hasElemtype());
  std::vector<LLExpr*> args;
  LLVar* arr = parseTermVar(e.getParts()[0]);
  const pb::PbArrayLiteral::Reader lit = e.getArraylit();
  for (auto ent : lit.getEntries()) {
    args.push_back(parseArrayEntry(ent));
  }
  return new LLArrayLiteral(TypeAST_from_pb(e.getElemtype()), arr, args);
}

LLExpr* parseByteArray(const pb::Letable::Reader& e) {
  return new LLByteArray(std::string(e.getBytesvalue().begin(),
                                     e.getBytesvalue().end()));
}

LLOccurrence* parseOccurrence(const pb::Letable::Reader& e) {
  const pb::PbOccurrence::Reader& o = e.getOcc();

  LLOccurrence* rv = new LLOccurrence;
  for (auto oo : o.getOccoffset()) {
    rv->offsets.push_back(oo);
  }
  for (auto oc : o.getOccctors()) {
    rv->ctors.push_back(parseCtorInfo(oc));
  }
  rv->var = parseTermVar(o.getScrutinee());

  return rv;
}

LLSwitch* parseSwitch(const pb::Terminator::Reader& b) {
  const pb::PbSwitch::Reader& sc = b.getScase();

  std::vector<CtorId> ctors;
  for (auto ctor : sc.getCtors()) {
    ctors.push_back(parseCtorId(ctor));
  }

  std::vector<std::string> ids;
  for (auto blockid : sc.getBlocks()) {
    ids.push_back(blockid);
  }

  std::string def;
  if (sc.hasDefCase()) { def = sc.getDefCase(); }

  LLVar* scrutinee = parseTermVar(sc.getVar());

  ASSERT(sc.hasCtorby());
  CtorTagRepresentation ctor_by = CTR_BareValue;
  if (sc.getCtorby() == "MASK3") ctor_by = CTR_MaskWith3;
  if (sc.getCtorby() == "INDIR") ctor_by = CTR_OutOfLine;
  if (sc.getCtorby() == "VALUE") ctor_by = CTR_BareValue;
  //DDiag() << "switch on " << scrutinee->name << " with ctor by " << sc.ctor_by();

  return new LLSwitch(scrutinee, ctors, ids, def, ctor_by);
}

LLExpr* parseDeref(const pb::Letable::Reader& e) {
  return new LLDeref(parseTermVar( e.getParts()[0]));
}

LLExpr* parseStore(const pb::Letable::Reader& e) {
  return new LLStore(
      parseTermVar( e.getParts()[0]),
      parseTermVar( e.getParts()[1]));
}

LLExpr* parseObjectCopy(const pb::Letable::Reader& e) {
  return new LLObjectCopy(
      parseTermVar( e.getParts()[0]),
      parseTermVar( e.getParts()[1]));
}

LLExpr* parseUnboxedTuple(const pb::Letable::Reader& e) {
  std::vector<LLVar*> args;
  for (auto p : e.getParts()) {
    args.push_back(parseTermVar(p));
  }
  return new LLUnboxedTuple(args);
}

LLExpr* parseKillProcess(const pb::Letable::Reader& e) {
  return new LLKillProcess(e.getStringvalue());
}

LLExpr* parseUnitValue(const pb::Letable::Reader& e) { return new LLUnitValue(); }

} // unnamed namespace

////////////////////////////////////////////////////////////////////

LLDecl* parseDecl(const pb::Decl::Reader& e) {
  return new LLDecl(    e.getName(),
        TypeAST_from_pb(e.getType()));
}

LLModule* LLModule_from_capnp(const foster::be::Module::Reader& e) {
  string moduleName = e.hasModulename() ? e.getModulename() : "";
  // Walk the type declarations and add their types to the current scope.
  // In contrast, the extern value declarations are only for checking purposes;
  // if a value isn't in a Module we've imported, we can't magically summon it!
  std::vector<NamedTypeAST*> namedTypes;
  for (auto td : e.getTypdecls()) {
    namedTypes.push_back(new NamedTypeAST(td.getName(), NULL,
                         foster::SourceRange::getEmptyRange()));
    ParsingContext::insertType(td.getName(),
                               namedTypes.back());
  }

  // We use an indirection through NamedTypeAST to break cyclic references.
  std::vector<LLDecl*> datatype_decls;
  { int i = 0;
    for (auto td : e.getTypdecls()) {
      LLDecl* d = parseDecl(td);
      namedTypes[i]->setNamedType(d->getType());
      datatype_decls.push_back(d);
      ++i;
    }
  }

  std::vector<LLProc*> procs;
  for (auto p : e.getProcs()) {
    procs.push_back(parseProc(p));
  }

  std::vector<LLDecl*> evdecls;
  for (auto evd : e.getExternvaldecls()) {
    evdecls.push_back(parseDecl(evd));
  }

  return new LLModule(moduleName, procs, evdecls, datatype_decls);
}


LLExpr* LLExpr_from_pb(const be::Letable::Reader& e) {
  LLExpr* rv = NULL;

  switch (e.getTag()) {
  case pb::Letable::Tag::ILBOOL:        rv = parseBool(e); break;
  case pb::Letable::Tag::ILCALL:        rv = parseCall(e); break;
  case pb::Letable::Tag::ILCALLPRIMOP: rv = parseCallPrimOp(e); break;
  case pb::Letable::Tag::ILINT:         rv = parseInt(e); break;
  case pb::Letable::Tag::ILFLOAT:       rv = parseFloat(e); break;
  case pb::Letable::Tag::ILTEXT:        rv = parseText(e); break;
  case pb::Letable::Tag::ILUNIT:        rv = parseUnitValue(e); break;
  case pb::Letable::Tag::ILDEREF:       rv = parseDeref(e); break;
  case pb::Letable::Tag::ILSTORE:       rv = parseStore(e); break;
  case pb::Letable::Tag::ILBITCAST:     rv = parseBitcast(e); break;
  case pb::Letable::Tag::ILARRAYREAD:  rv = parseArrayRead(e); break;
  case pb::Letable::Tag::ILARRAYPOKE:  rv = parseArrayPoke(e); break;
  case pb::Letable::Tag::ILARRAYLENGTH:rv = parseArrayLength(e); break;
  case pb::Letable::Tag::ILARRAYLITERAL:rv = parseArrayLiteral(e); break;
  case pb::Letable::Tag::ILBYTEARRAY:  rv = parseByteArray(e); break;
  case pb::Letable::Tag::ILALLOCATE:    rv = parseAllocate(e); break;
  case pb::Letable::Tag::ILOCCURRENCE:  rv = parseOccurrence(e); break;
  case pb::Letable::Tag::ILOBJECTCOPY: rv = parseObjectCopy(e); break;
  case pb::Letable::Tag::ILUNBOXEDTUPLE:rv =parseUnboxedTuple(e); break;
  case pb::Letable::Tag::ILKILLPROCESS:rv = parseKillProcess(e); break;

  default:
    EDiag() << "Unknown protobuf tag: " << int(e.getTag());
    break;
  }

  if (!rv) {
    EDiag() << "Unable to reconstruct LLExpr from protobuf Expr"
            << " with tag # " << int(e.getTag()) << "\n";
  } else if (e.hasType()) {
    rv->type = TypeAST_from_pb(e.getType());
  }

  return rv;
}

////////////////////////////////////////////////////////////////////

FnTypeAST* parseProcType(const pb::ProcType::Reader& fnty) {
  ASSERT(fnty.hasRettype()) << "\n\tCannot build FnTypeAST without a return type in the protobuf";

  TypeAST* retTy = TypeAST_from_pb(fnty.getRettype());
  ASSERT(retTy) << "\n\tCannot build FnTypeAST if the protobuf's"
                << " return type can't be reconstructed.\n";

  std::vector<TypeAST*> argTypes;
  for (auto ty : fnty.getArgtypes()) {
    argTypes.push_back(TypeAST_from_pb(ty));
  }

  ASSERT(fnty.hasCallingconvention())
    << "must provide calling convention for all function types!";
  std::map<std::string, std::string> annots;
  annots["callconv"] = fnty.getCallingconvention();

  return new FnTypeAST(retTy, argTypes, NULL, annots);
}


DataCtor* parseDataCtor(const pb::PbDataCtor::Reader ct) {
  DataCtor* c = new DataCtor;
  c->name = ct.getName();
  for (auto ty : ct.getType()) {
    c->types.push_back(TypeAST_from_pb(ty));
  }
  return c;
}

std::vector<DataCtor*> parseDataCtors(const pb::Type::Reader& t) {
  std::vector<DataCtor*> rv;
  for (auto ctor : t.getCtor()) {
    rv.push_back(parseDataCtor(ctor));
  }
  return rv;
}

TypeAST* TypeAST_from_pb(const pb::Type::Reader& t) {
  switch (t.getTag()) {
  case pb::Type::Tag::ARRAY:
    ASSERT(t.getTypeparts().size() == 1);
    return ArrayTypeAST::get(TypeAST_from_pb(t.getTypeparts()[0]));

  case pb::Type::Tag::PTR:
    ASSERT(t.getTypeparts().size() == 1);
    return RefTypeAST::get(TypeAST_from_pb(t.getTypeparts()[0]));

  case pb::Type::Tag::PROCTY:
    return parseProcType(t.getProcty());

  case pb::Type::Tag::STRUCT: {
    std::vector<TypeAST*> parts;
    for (auto p : t.getTypeparts()) {
      parts.push_back(TypeAST_from_pb(p));
    }
    return StructTypeAST::get(parts);
  }

  case  pb::Type::Tag::CORO: {
    ASSERT(t.getTypeparts().size() == 2)
        << "coro must have base and arg types,"
        << " but #type parts is " << t.getTypeparts().size();
    TypeAST* targ = TypeAST_from_pb(t.getTypeparts()[0]);
    TypeAST* tret = TypeAST_from_pb(t.getTypeparts()[1]);
    return CoroTypeAST::get(targ, tret);
  }

  case pb::Type::Tag::NAMED: {
    const string& tyname = t.getName();

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

  case pb::Type::Tag::FLOAT64:
    return PrimitiveTypeAST::get("Float64",
                             llvm::Type::getDoubleTy(llvm::getGlobalContext()));

  case pb::Type::Tag::PRIMINT: {
    int size = t.getCarraysize()[0];

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

  case pb::Type::Tag::DATATYPE: {
    const string& tyname = t.getName();
    return new DataTypeAST(tyname, parseDataCtors(t),
                           SourceRange::getEmptyRange());
  }

  default:
    EDiag() << "found unexpected type in protobuf!\n";
    return NULL;
  }
}

} // namespace foster
