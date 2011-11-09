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
  class Function;
  class AllocaInst;
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


struct LLBlock {
  std::string block_id;
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
  string name;
  FnTypeAST* type;
  llvm::GlobalValue::LinkageTypes functionLinkage;
  std::vector<std::string> argnames;
  std::vector<LLBlock*> blocks;
  llvm::Function* F;

  explicit LLProc(FnTypeAST* procType, const string& name,
          const std::vector<std::string>& argnames,
          llvm::GlobalValue::LinkageTypes linkage, std::vector<LLBlock*> blocks)
  : name(name), type(procType), functionLinkage(linkage),
    argnames(argnames), blocks(blocks), F(NULL) {}

  FnTypeAST* getFnType() { return type; }
  const std::string& getName() const { return name; }
  virtual void codegenProc(CodegenPass* pass);
  virtual void codegenProto(CodegenPass* pass);
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
  explicit LLBool(string val)
    : LLExpr("LLBool"), boolValue(val == "true") {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLVar : public LLExpr {
  string name;
  // Type is not used

  explicit LLVar(const string& name) : LLExpr("LLVar"),
        name(name) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
  const string getName() const { return name; }
};

struct LLGlobalSymbol : public LLVar {
  LLGlobalSymbol(std::string name) : LLVar(name) {}
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
  llvm::Value* codegenStorage(CodegenPass* pass);
  void codegenTo(CodegenPass* pass, llvm::Value* tup_ptr);
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// base[index]
struct LLArrayRead : public LLExpr {
  LLVar* base;
  LLVar* index;
  explicit LLArrayRead(LLVar* base, LLVar* index)
    : LLExpr("LLArrayRead"), base(base), index(index) {
    }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// val >^ base[index]
struct LLArrayPoke : public LLExpr {
  LLVar* value;
  LLVar* base;
  LLVar* index;
  explicit LLArrayPoke(LLVar* v, LLVar* b, LLVar* i)
    : LLExpr("LLArrayPoke"), value(v), base(b), index(i) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLClosure {
  std::string varname;
  std::string envname;
  std::string procname;
  LLTuple*    env;
  explicit LLClosure(const std::string& _varn,
                     const std::string& _envn,
                     const std::string& _proc,
                     LLTuple* _env)
    : varname(_varn), envname(_envn), procname(_proc), env(_env) {
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
  bool unboxed;
  enum MemRegion {
      MEM_REGION_STACK
    , MEM_REGION_GLOBAL_HEAP
  } region;
  bool isStackAllocated() const { return region == MEM_REGION_STACK; }

  explicit LLAllocate(TypeAST* t, int8_t c, bool u, LLVar* arrSize, MemRegion m)
     : LLExpr("LLAllocate"), arraySize(arrSize), ctorId(c), unboxed(u),
         region(m) { this->type = t; }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLAlloc : public LLExpr {
  LLVar* baseVar;
  explicit LLAlloc(LLVar* e) : LLExpr("LLAlloc"), baseVar(e) {}
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

struct DecisionTree;

struct Occurrence {
  std::vector<int> offsets;
  std::vector<CtorId> ctors;
};

struct CaseContext;

struct SwitchCase {
  std::vector<CtorId>        ctors;
  std::vector<DecisionTree*> trees;
  DecisionTree*        defaultCase;
  Occurrence*                  occ;
  void codegenSwitch(CodegenPass* pass, llvm::Value* scrutinee, CaseContext* ctx);
};

typedef std::pair<std::string, Occurrence*> DTBinding;

struct DecisionTree {
  enum Tag {
    DT_FAIL, DT_LEAF, DT_SWITCH
  } tag;
  TypeAST* type;
  std::vector<DTBinding> binds; std::string action_block_id;
  SwitchCase* sc;
  DecisionTree() : tag(DT_FAIL), type(NULL), sc(NULL) {}
  DecisionTree(std::vector<DTBinding> binds, std::string b_id)
                 : tag(DT_LEAF), type(NULL), binds(binds),
                                      action_block_id(b_id), sc(NULL) {}
  DecisionTree(SwitchCase* sc) : tag(DT_SWITCH), type(NULL), sc(sc) {}
  void codegenDecisionTree(CodegenPass* pass, llvm::Value* scrutinee,
                           CaseContext* ctx);
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
  explicit LLBr(std::string b) : block_id(b) {}
  virtual void codegenTerminator(CodegenPass* pass);
};

struct LLCondBr : public LLTerminator {
  std::string then_id;
  std::string else_id;
  LLVar* var;
  explicit LLCondBr(std::string b, std::string b2, LLVar* v)
        : then_id(b), else_id(b2), var(v) {}
  virtual void codegenTerminator(CodegenPass* pass);
};

struct LLSwitch : public LLTerminator {
  LLVar* scrutinee;
  DecisionTree* dt;
  TypeAST* branchType;

  LLSwitch(LLVar* testExpr, TypeAST* ty, DecisionTree* dt)
    : scrutinee(testExpr), dt(dt), branchType(ty) {
  }
  virtual void codegenTerminator(CodegenPass* pass);
};

#endif // header guard

