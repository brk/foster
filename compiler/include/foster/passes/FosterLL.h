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
#include "llvm/GlobalValue.h"

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

class LLVar;
class LLExpr;
class TypeAST;
class FnTypeAST;

struct CodegenPass;

std::ostream& operator<<(std::ostream& out, LLExpr& expr);

///////////////////////////////////////////////////////////

struct LLTerminator {
  virtual void codegenTerminator(CodegenPass* pass) = 0;
};

struct LLMiddle {
  virtual void codegenMiddle(CodegenPass* pass) = 0;
};

struct LLRebindId : public LLMiddle {
  std::string from; LLVar* to;
  explicit LLRebindId(std::string from, LLVar* to) : from(from), to(to) {}
  virtual void codegenMiddle(CodegenPass* pass);
};

struct LLBitcast : public LLMiddle {
  std::string from; LLVar* to;
  explicit LLBitcast(std::string from, LLVar* to) : from(from), to(to) {}
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
};

class LLProc;
class LLAllocate;

struct LLDecl {
  string name;
  TypeAST* type;
  explicit LLDecl(const string& name, TypeAST* type)
      : name(name), type(type) {}
  llvm::Value* codegen(CodegenPass* pass);
  const string getName() const { return name; }
  TypeAST*     getType() const { return type; }
};

struct LLModule {
  const std::string name;
  std::vector<LLProc*> procs;
  std::vector<LLDecl*> val_decls;
  std::vector<LLDecl*> datatype_decls;

  explicit LLModule(const std::string& name,
                    const std::vector<LLProc*>& procs,
                    const std::vector<LLDecl*> vdecls,
                    const std::vector<LLDecl*> datatype_decls)
  : name(name), procs(procs), val_decls(vdecls), datatype_decls(datatype_decls) {}

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
  std::string cleanText;
  std::string originalText;
  llvm::APInt* apint;

public:
  explicit LLInt(const std::string& cleanTextBase10, int activeBits)
    : LLExpr("LLInt") {
    // Debug builds of LLVM don't ignore leading zeroes when considering
    // needed bit widths.
    int bitsLLVMneeds = (std::max)(intSizeForNBits(activeBits),
                                   (unsigned) cleanText.size());
    int ourSize = intSizeForNBits(bitsLLVMneeds);
    apint = new llvm::APInt(ourSize, cleanTextBase10, 10);
    type = TypeAST::i(ourSize);
  }

  virtual llvm::Value* codegen(CodegenPass* pass);
  llvm::APInt& getAPInt() { return *apint; }

  unsigned intSizeForNBits(unsigned n) const {
  // Disabled until we get better inferred literal types
    //if (n <= 1) return 1;
    //if (n <= 8) return 8;
    //if (n <= 16) return 16;
    if (n <= 32) return 32;
    if (n <= 64) return 64;
    ASSERT(false) << "Support for arbitrary-precision ints not yet implemented.";
    return 0;
  }
};

struct LLBool : public LLExpr {
  bool boolValue;
  explicit LLBool(string val) : LLExpr("LLBool"), boolValue(val == "true") {}
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
};

// This class permits direct injection of LLVM values to be injected
// back up into the LLExpr/codegen layer.
struct LLValueVar : public LLVar {
  llvm::Value* val;
  LLValueVar(llvm::Value* v) : LLVar(""), val(v) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// base(args)
struct LLCall : public LLExpr {
  LLExpr* base;
  // Calls may be to non-var bases (LLCoroPrim, etc)
  // because we lazily generate polymorphic instantiations.
  std::vector<LLVar*> args;
  bool callMightTriggerGC;
  LLCall(LLExpr* base, std::vector<LLVar*>& args, bool mayGC)
  : LLExpr("LLCall"), base(base), args(args), callMightTriggerGC(mayGC) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct CtorId {
  string typeName;
  string ctorName;
  int smallId;
};

struct LLAppCtor : public LLExpr {
  std::vector<LLVar*> args;
  CtorId ctorId;
  LLAppCtor(CtorId c, std::vector<LLVar*>& _args)
  : LLExpr("LLAppCtor"), args(_args), ctorId(c) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLCallPrimOp : public LLExpr {
  std::vector<LLVar*> args;
  std::string op;
  LLCallPrimOp(std::string _op, std::vector<LLVar*>& _args)
  : LLExpr("LLCallPrimOp"), args(_args), op(_op) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLTuple : public LLExpr {
  std::vector<LLVar*> vars;
  const char* typeName;
  LLAllocate* allocator;

  explicit LLTuple(const std::vector<LLVar*>& vars, LLAllocate* a)
    : LLExpr("LLTuple"), vars(vars),
      typeName("tuple"), allocator(a) {}
  llvm::Value* codegenStorage(CodegenPass* pass, bool init);
  llvm::Value* codegenObjectOfSlot(llvm::Value* slot);
  void codegenTo(CodegenPass* pass, llvm::Value* tup_ptr);
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLArrayIndex {
  LLVar* base;
  LLVar* index;
  std::string static_or_dynamic;
  explicit LLArrayIndex(LLVar* base, LLVar* index, string static_or_dynamic)
    : base(base), index(index), static_or_dynamic(static_or_dynamic) {}
  virtual llvm::Value* codegenARI(CodegenPass* pass);
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

struct LLClosure {
  std::string varname;
  std::string envname;
  std::string procname;
  std::string srclines;
  LLTuple*    env;
  explicit LLClosure(const std::string& _varn,
                     const std::string& _envn,
                     const std::string& _proc,
                     const std::string& _srcs,
                     LLTuple* _env)
    : varname(_varn), envname(_envn), procname(_proc), srclines(_srcs),
      env(_env) {
   env->typeName = "env";
 }
 llvm::Value* codegenClosure(CodegenPass* pass, llvm::Value* envSlot);
};

struct LLClosures : public LLMiddle {
  std::vector<LLClosure*> closures;
  explicit LLClosures(std::vector<LLClosure*>& closures)
    { this->closures = closures; }
  virtual void codegenMiddle(CodegenPass* pass);
};

struct LLLetVals : public LLMiddle {
  std::vector<std::string> names;
  std::vector<LLExpr*>     exprs;
  explicit LLLetVals(const std::vector<std::string>& names,
                     const std::vector<LLExpr*>&     exprs)
  : names(names), exprs(exprs) {}

  virtual void codegenMiddle(CodegenPass* pass);
};

struct LLAllocate : public LLExpr {
  LLVar* arraySize; // NULL if not allocating an array
  int8_t ctorId;
  enum MemRegion {
      MEM_REGION_STACK
    , MEM_REGION_GLOBAL_HEAP
  } region;
  std::string srclines;

  bool isStackAllocated() const { return region == MEM_REGION_STACK; }

  explicit LLAllocate(TypeAST* t, int8_t c, LLVar* arrSize, MemRegion m,
                      std::string allocsite)
     : LLExpr("LLAllocate"), arraySize(arrSize), ctorId(c), region(m),
                             srclines(allocsite) { this->type = t; }
  llvm::Value* codegenCell(CodegenPass* pass, bool init);
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLAlloc : public LLExpr {
  LLVar* baseVar;
  LLAllocate::MemRegion region;
  explicit LLAlloc(LLVar* e, LLAllocate::MemRegion r)
      : LLExpr("LLAlloc"), baseVar(e), region(r) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLDeref : public LLExpr {
  LLVar* base;
  explicit LLDeref(LLVar* e) : LLExpr("LLDeref"), base(e) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLStore : public LLExpr {
  LLVar* v; LLVar* r;
  explicit LLStore(LLVar* v, LLVar* r)
    : LLExpr("LLStore"), v(v), r(r) {}
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
  std::vector<CtorId> ctors;
  explicit LLOccurrence() : LLExpr("LLOccurrence") {}
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

struct LLSwitch : public LLTerminator {
  std::vector<CtorId> ctors;
  std::vector<std::string> blockids;
  std::string defaultCase;
  LLOccurrence* occ;
  LLSwitch(LLOccurrence* _occ,
           const std::vector<CtorId>& _ctors,
           const std::vector<std::string>& _ids,
           const std::string& _def)
    : ctors(_ctors), blockids(_ids), defaultCase(_def), occ(_occ) {}

  virtual void codegenTerminator(CodegenPass* pass);
};

#endif // header guard

