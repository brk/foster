// Copyright (c) 2009-2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_LL_H
#define FOSTER_LL_H

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "parse/FosterSymbolTable.h"
#include "parse/FosterTypeAST.h"

#include "llvm/ADT/APInt.h"
#include "llvm/IR/GlobalValue.h"

#include <vector>
#include <string>

using std::string;

namespace llvm {
  class Type;
  class Value;
  class APInt;
  class PHINode;
  class Function;
  class AllocaInst;
  class BasicBlock;
}

using llvm::Value;

struct LLVar;
struct LLExpr;
class TypeAST;
class FnTypeAST;
struct LLTupleStore;

struct CodegenPass;
struct CodegenPassConfig {
  bool useNSW;
  bool useNUW;
  bool trackAllocSites;
  bool countClosureCalls;
  bool emitLifetimeInfo;
  bool disableAllArrayBoundsChecks;
  bool disableInliningOnAllFosterFunctions;
  bool standalone;
};

std::ostream& operator<<(std::ostream& out, LLExpr& expr);

///////////////////////////////////////////////////////////

struct LLTerminator {
  virtual void codegenTerminator(CodegenPass* pass) = 0;
  virtual ~LLTerminator() {}
};

struct LLMiddle {
  virtual void codegenMiddle(CodegenPass* pass) = 0;
  virtual ~LLMiddle() {}
};

struct LLRebindId : public LLMiddle {
  std::string from; LLVar* to;
  explicit LLRebindId(std::string from, LLVar* to) : from(from), to(to) {}
  virtual void codegenMiddle(CodegenPass* pass);
};

struct LLBlock {
  std::string block_id;
  int numPreds;
  llvm::BasicBlock* bb;
  std::vector<LLVar*> phiVars;
  std::vector<llvm::PHINode*> phiNodes;
  std::vector<LLMiddle*> mids;
  LLTerminator* terminator;

  void codegenBlock(CodegenPass* pass);
};

///////////////////////////////////////////////////////////

struct LLExpr {
  TypeAST* type;
  const char* const tag;

  explicit LLExpr(const char* const tag) : type(NULL), tag(tag) {}
  virtual ~LLExpr() {}

  virtual llvm::Value* codegen(CodegenPass* pass) = 0;
  virtual llvm::Value* codegenCallee(CodegenPass* pass) { return codegen(pass); }
};

struct LLProc;
struct LLAllocate;

struct LLDecl {
  string name;
  TypeAST* type;
  bool isForeign;
  bool autoDeref;
  explicit LLDecl(const string& name, TypeAST* type, bool isForeign)
      : name(name), type(type), isForeign(isForeign), autoDeref(false) {}
  const string getName() const { return name; }
  TypeAST*     getType() const { return type; }
};

struct LLArrayLiteral : public LLExpr {
  TypeAST* elem_type;
  LLVar* arr;
  std::vector<LLExpr*> args;
  explicit LLArrayLiteral(TypeAST* elem_type, LLVar* arr, std::vector<LLExpr*> args)
        : LLExpr("LLArrayLiteral"), elem_type(elem_type), arr(arr), args(args) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLTopItem {
  string   name;
  LLArrayLiteral*  arrlit;
  LLExpr*  lit;

  explicit LLTopItem(const string& name, LLArrayLiteral* arrlit)
      : name(name), arrlit(arrlit), lit(nullptr) {}

  explicit LLTopItem(const string& name, LLExpr* elit)
      : name(name), arrlit(nullptr), lit(elit) {}
};

struct LLModule {
  const std::string name;
  std::vector<LLProc*> procs;
  std::vector<LLDecl*> extern_val_decls;
  std::vector<LLDecl*> datatype_decls;
  std::vector<LLTopItem*> items;

  explicit LLModule(const std::string& name,
                    const std::vector<LLProc*>& procs,
                    const std::vector<LLDecl*> edecls,
                    const std::vector<LLDecl*> datatype_decls,
                    const std::vector<LLTopItem*> items)
  : name(name), procs(procs), extern_val_decls(edecls),
    datatype_decls(datatype_decls), items(items) {}

  void codegenModule(CodegenPass* pass);
};

struct LLProc {
private:
  llvm::Function* F; // will be initialized when codegenning proto
protected:
  FnTypeAST* type; // will be mutated (to be marked as proc) when codegenning proto
public:
  explicit LLProc() : F(NULL) {}
  virtual ~LLProc() {}

  void codegenProc(CodegenPass* pass); // These two functions are common to all procs
  void codegenProto(CodegenPass* pass);

  FnTypeAST* getFnType()  const { ASSERT(type); return type; }
  llvm::Function* getFn() const { ASSERT(F);    return F; }

  virtual llvm::GlobalValue::LinkageTypes getFunctionLinkage() const = 0;
  virtual std::vector<std::string>        getFunctionArgNames() const = 0;
  virtual const std::string getName() const = 0;
  virtual const std::string getCName() const = 0;
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F) = 0;
};

struct LLProcCFG : public LLProc {
private:
  string name;
  llvm::GlobalValue::LinkageTypes functionLinkage;
  std::vector<std::string> argnames;
  std::vector<LLBlock*> blocks;

public:
  explicit LLProcCFG(FnTypeAST* procType, const string& name,
                     const std::vector<std::string>& argnames,
                     llvm::GlobalValue::LinkageTypes linkage,
                     std::vector<LLBlock*> blocks)
  : name(name), functionLinkage(linkage), argnames(argnames), blocks(blocks) {
      this->type = procType;
  }
  virtual ~LLProcCFG() {}

  virtual llvm::GlobalValue::LinkageTypes getFunctionLinkage() const { return functionLinkage; }
  virtual std::vector<std::string>        getFunctionArgNames() const { return argnames; }
  virtual const std::string getName() const { return name; }
  virtual const std::string getCName() const { return name; }
  virtual void codegenToFunction(CodegenPass* pass, llvm::Function* F);
};

////////////////////////////////////////////////////////////////

struct IntAST;

struct LLInt : public LLExpr {
private:
  llvm::APInt* apint;

public:
  explicit LLInt(const std::string& cleanTextBase10, int bitSize)
    : LLExpr("LLInt") {
    // Debug builds of LLVM don't ignore leading zeroes when considering
    // needed bit widths.
    int bitsLLVMneeds = (std::max)(intSizeForNBits(bitSize),
                                   (unsigned) cleanTextBase10.size());
    int ourSize = intSizeForNBits(bitsLLVMneeds);
    ASSERT(ourSize > 0) << "Support for arbitrary-precision ints "
                  << "(bit size " << bitsLLVMneeds << ") not yet implemented "
                  << "for integer " << cleanTextBase10;
    ASSERT(abs(bitSize) <= ourSize) << "Integer '" << cleanTextBase10 << "' had "
                               << bitSize << " bits; needed " << ourSize;
    apint = new llvm::APInt(ourSize, cleanTextBase10, 10);
  }

  virtual llvm::Value* codegen(CodegenPass* pass);
  llvm::APInt& getAPInt() { return *apint; }

  unsigned intSizeForNBits(int n) const {
    if (n == -32) return getWordTySize();
    if (n == -64) return getWordTySize() * 2;
    if (n <= 1)  return 1;
    if (n <= 8)  return 8;
    if (n <= 16) return 16;
    if (n <= 32) return 32;
    if (n <= 64) return 64;
    if (n == 128) return 128;
    return 0;
  }
};

struct LLBool : public LLExpr {
  bool boolValue;
  explicit LLBool(bool val) : LLExpr("LLBool"), boolValue(val) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLFloat : public LLExpr {
  double doubleValue;
  explicit LLFloat(double dval) : LLExpr("LLFloat"), doubleValue(dval) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLText : public LLExpr {
  std::string stringValue;
  explicit LLText(const string& val) : LLExpr("LLText"), stringValue(val) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLVar : public LLExpr {
  string name;
  // Type is not used
  explicit LLVar(const string& name) : LLExpr("LLVar"), name(name) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
  const string getName() const { return name; }
};

struct LLGlobalSymbol : public LLVar {
  LLGlobalSymbol(std::string name) : LLVar(name) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
  virtual llvm::Value* codegenCallee(CodegenPass* pass);
};

// This class permits direct injection of LLVM values to be injected
// back up into the LLExpr/codegen layer.
struct LLValueVar : public LLVar {
  llvm::Value* val;
  LLValueVar(llvm::Value* v) : LLVar(""), val(v) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLBitcast : public LLExpr {
  LLVar* var;
  explicit LLBitcast(LLVar* var) : LLExpr("LLBitcast"), var(var) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// base(args)
struct LLCall : public LLExpr {
  LLExpr* base;
  // Calls may be to non-var bases (LLCoroPrim, etc)
  // because we lazily generate polymorphic instantiations.
  std::vector<LLVar*> args;
  bool callMightTriggerGC;
  bool okToMarkAsTailCall;
  std::string callconv;

  LLCall(LLExpr* base, std::vector<LLVar*>& args, bool mayGC, bool tail, std::string callconv)
  : LLExpr("LLCall"), base(base), args(args), callMightTriggerGC(mayGC),
                      okToMarkAsTailCall(tail), callconv(callconv) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct CtorRepr {
  bool isTransparent;
  bool isNullary;
  bool isBoxed;
  int64_t smallId; // small in the common case, at least,
                   // but must be large enough to fit any integer
                   // constant that might be pattern-matched against.
  CtorRepr() : isTransparent(false), isNullary(false), isBoxed(true), smallId(0) { }
};

inline std::string str(const CtorRepr& r) {
  std::string rv;
  if (r.isTransparent) rv += "Transparent";
  if (r.isNullary) rv += "Nullary";
  if (!r.isTransparent && !r.isNullary) rv += "Default";
  if (r.isBoxed) rv += "Boxed"; else rv += "Unboxed";
  return rv;
}

struct CtorId {
  string typeName;
  string ctorName;
  CtorRepr ctorRepr;
};

struct CtorInfo {
  StructTypeAST* ctorStructType; // or NULL
  CtorId         ctorId;
};

struct LLCallPrimOp : public LLExpr {
  std::vector<LLVar*> args;
  std::string op;
  int64_t tag;
  LLCallPrimOp(std::string _op, int64_t _tag, std::vector<LLVar*>& _args)
  : LLExpr("LLCallPrimOp"), args(_args), op(_op), tag(_tag) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLCallInlineAsm : public LLExpr {
  std::vector<LLVar*> args;
  std::string asmString;
  std::string constraints;
  bool hasSideEffects;
  FnTypeAST* ty;

  LLCallInlineAsm(FnTypeAST*  _ty,
                  std::string _asmString,
                  std::string _constraints,
                  bool        _hasSideEffects,
                  std::vector<LLVar*>& _args)
  : LLExpr("LLCallInlineAsm"), args(_args), asmString(_asmString),
      constraints(_constraints),
      hasSideEffects(_hasSideEffects), ty(_ty) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLUnitValue : public LLExpr {
  explicit LLUnitValue() : LLExpr("LLUnitValue") {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLArrayIndex {
  LLVar* base;
  LLVar* index;
  std::string static_or_dynamic;
  std::string srclines;
  explicit LLArrayIndex(LLVar* base, LLVar* index,
                        string static_or_dynamic, string srclines)
    : base(base), index(index),
      static_or_dynamic(static_or_dynamic), srclines(srclines) {}
  llvm::Value* codegenARI(CodegenPass* pass, Value** base, llvm::Type* ty);
};

// base[index]
struct LLArrayRead : public LLExpr {
  LLArrayIndex* ari;
  explicit LLArrayRead(LLArrayIndex* ari) : LLExpr("LLArrayRead"), ari(ari) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// val >^ base[index]
struct LLArrayPoke : public LLExpr {
  LLVar* value;
  LLArrayIndex* ari;
  explicit LLArrayPoke(LLArrayIndex* ari, LLVar* v)
    : LLExpr("LLArrayPoke"), value(v), ari(ari) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLArrayLength : public LLExpr {
  LLVar* value;
  explicit LLArrayLength(LLVar* v) : LLExpr("LLArrayLength"), value(v) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};


// Conceptually redundant, but more efficient at representing large byte arrays.
struct LLByteArray : public LLExpr {
  std::string bytes;
  explicit LLByteArray(std::string b) : LLExpr("LLByteArray"), bytes(b) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLLetVals : public LLMiddle {
  std::vector<std::string> names;
  std::vector<LLExpr*>     exprs;
  explicit LLLetVals(const std::vector<std::string>& names,
                     const std::vector<LLExpr*>&     exprs)
  : names(names), exprs(exprs) {}

  virtual void codegenMiddle(CodegenPass* pass);
};

struct LLTupleStore : public LLMiddle {
  std::vector<LLVar*> vars;
  LLVar* storage;
  bool storage_indir;

  explicit LLTupleStore(const std::vector<LLVar*>& vars, LLVar* s, bool indir)
                 : vars(vars), storage(s), storage_indir(indir) {}
  void codegenMiddle(CodegenPass* pass) override;
};

struct LLUnboxedTuple : public LLExpr {
  std::vector<LLVar*> vars;
  bool isStatic;

  explicit LLUnboxedTuple(const std::vector<LLVar*>& vars, bool isStatic)
    : LLExpr("LLUnboxedTuple"), vars(vars), isStatic(isStatic) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct SourceLoc {
  int32_t line;
  int32_t col;
  std::string file;
};

struct LLAllocate : public LLExpr {
  LLVar* arraySize; // NULL if not allocating an array
  CtorRepr ctorRepr;
  std::string type_name;
  enum MemRegion {
      MEM_REGION_STACK
    , MEM_REGION_GLOBAL_HEAP
    , MEM_REGION_GLOBAL_DATA
  } region;
  std::string typedesc;
  bool zero_init;
  SourceLoc loc;

  bool isStackAllocated() const { return region == MEM_REGION_STACK; }

  explicit LLAllocate(TypeAST* t, std::string tynm,
                      CtorRepr cr, LLVar* arrSize, MemRegion m,
                      std::string allocsite, bool zero_init, SourceLoc loc)
     : LLExpr("LLAllocate"), arraySize(arrSize), ctorRepr(cr), type_name(tynm),
                             region(m), typedesc(allocsite),
                             zero_init(zero_init), loc(loc) { this->type = t; }
  llvm::Value* codegenCell(CodegenPass* pass, bool init);
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLDeref : public LLExpr {
  LLVar* base;
  bool isTraced;
  explicit LLDeref(LLVar* e, bool isTraced)
    : LLExpr("LLDeref"), base(e), isTraced(isTraced) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLStore : public LLExpr {
  LLVar* v; LLVar* r;
  bool isTraced;
  explicit LLStore(LLVar* v, LLVar* r, bool isTraced)
    : LLExpr("LLStore"), v(v), r(r), isTraced(isTraced) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLCoroPrim : public LLExpr {
  string   primName;
  TypeAST* retType;
  TypeAST* typeArg;
  explicit LLCoroPrim(string primName, TypeAST* ret, TypeAST* arg)
      : LLExpr("LLCoroPrim"), primName(primName),
        retType(ret), typeArg(arg) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLOccurrence : public LLExpr {
  LLVar* var;
  std::vector<int> offsets;
  std::vector<CtorInfo> ctors;
  explicit LLOccurrence() : LLExpr("LLOccurrence") {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLKillProcess : public LLExpr {
  std::string stringValue;
  explicit LLKillProcess(const string& val) : LLExpr("LLKillProcess"), stringValue(val) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLGlobalAppCtor : public LLExpr {
  std::vector<LLVar*> args;
  CtorInfo ctor;

  explicit LLGlobalAppCtor(CtorInfo ctor, std::vector<LLVar*> args)
    : LLExpr("LLGlobalAppCtor"), args(args), ctor(ctor) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

///////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////

struct LLRetVoid : public LLTerminator {
  virtual void codegenTerminator(CodegenPass* pass);
};

struct LLRetVal : public LLTerminator {
  LLVar* val;
  explicit LLRetVal(LLVar* v) : val(v) {}
  virtual void codegenTerminator(CodegenPass* pass);
};

struct LLBr : public LLTerminator {
  std::string block_id;
  std::vector<LLVar*> args;
  explicit LLBr(std::string b) : block_id(b) {}
  explicit LLBr(std::string b, const std::vector<LLVar*>& args)
                 : block_id(b), args(args) {}
  virtual void codegenTerminator(CodegenPass* pass);
};

enum CtorTagRepresentation {
  CTR_BareValue, // the default, for primitive types like unboxed integers.
  CTR_OutOfLine,
  CTR_MaskWith3 // mask to extract inline tag bits
};

struct LLSwitch : public LLTerminator {
  std::vector<CtorId> ctors;
  std::vector<std::string> blockids;
  std::string defaultCase;
  LLVar* var;
  CtorTagRepresentation ctr;
  LLSwitch(LLVar* _var,
           const std::vector<CtorId>& _ctors,
           const std::vector<std::string>& _ids,
           const std::string& _def,
           CtorTagRepresentation _ctr)
    : ctors(_ctors), blockids(_ids), defaultCase(_def), var(_var), ctr(_ctr) {}

  virtual void codegenTerminator(CodegenPass* pass);
};

#endif // header guard

