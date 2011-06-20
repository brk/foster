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

#include <vector>
#include <string>

using std::string;

namespace llvm {
  class Type;
  class Value;
  class APInt;
  class ConstantInt;
  class AllocaInst;
}

using llvm::Value;

class LLExpr;
class TypeAST;
class FnTypeAST;

std::ostream& operator<<(std::ostream& out, LLExpr& expr);

///////////////////////////////////////////////////////////

struct CodegenPass;

struct LLExpr {
  TypeAST* type;
  const char* const tag;

  explicit LLExpr(const char* const tag) : type(NULL), tag(tag) {}
  virtual ~LLExpr() {}

  virtual llvm::Value* codegen(CodegenPass* pass) = 0;
};

class LLInt;
class LLBool;
class LLTuple;
class LLSubscript;
class LLProc;
class LLIf;

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
  std::vector<LLDecl*> decls;

  explicit LLModule(const std::string& name,
                    const std::vector<LLProc*>& procs,
                    const std::vector<LLDecl*> decls)
  : name(name), procs(procs), decls(decls) {}

  void codegen(CodegenPass* pass);
};

struct LLProc {
  string name;
  FnTypeAST* type;
  std::vector<std::string> argnames;
  LLExpr* body;
  llvm::Value* value;

  explicit LLProc(FnTypeAST* procType, const string& name,
          const std::vector<std::string>& argnames, LLExpr* body)
    : name(name), type(procType), argnames(argnames), body(body) {
      value = NULL;
  }

  FnTypeAST* getFnType() { return type; }
  const std::string& getName() const { return name; }
  LLExpr*& getBody() { return body; }
  virtual llvm::Value* codegen(CodegenPass* pass);
  virtual llvm::Value* codegenProto(CodegenPass* pass);
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

// base(args)
struct LLCall : public LLExpr {
  LLVar* base;
  std::vector<LLVar*> args;
  LLCall(LLVar* base, std::vector<LLVar*>& args)
  : LLExpr("LLCall"), base(base), args(args) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLTuple : public LLExpr {
  std::vector<LLVar*> parts;
  bool isClosureEnvironment;
  explicit LLTuple(const std::vector<LLVar*>& vars)
    : LLExpr("LLTuple"),
      isClosureEnvironment(false) {
    parts = vars;
  }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// v[index]
struct LLSubscript : public LLExpr {
  LLVar * base;
  LLExpr* index;
  explicit LLSubscript(LLVar* base, LLExpr* index)
    : LLExpr("LLSubscript"), base(base), index(index) {
    }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLClosure {
  std::string varname;
  std::string procname;
  LLTuple*    env;
  explicit LLClosure(const std::string& varname,
                     const std::string& procname,
                     LLTuple* env)
    : varname(varname), procname(procname), env(env) {
   env->isClosureEnvironment = true;
 }
 virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLClosures : public LLExpr {
  LLExpr* expr;
  std::vector<LLClosure*> closures;
  explicit LLClosures(LLExpr* expr, std::vector<LLClosure*>& closures)
    : LLExpr("LLCLosures"), expr(expr) { this->closures = closures; }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLLetVals : public LLExpr {
  std::vector<std::string> names;
  std::vector<LLExpr*>     exprs;
  LLExpr* inexpr;
  explicit LLLetVals(const std::vector<std::string>& names,
                     const std::vector<LLExpr*>&     exprs, LLExpr* inexpr)
  : LLExpr("LLLetVals"), names(names), exprs(exprs), inexpr(inexpr) {}

  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLIf : public LLExpr {
  LLVar* cond;
  LLExpr* thenExpr;
  LLExpr* elseExpr;
  LLIf(LLVar* cond, LLExpr* thenExpr, LLExpr* elseExpr)
     : LLExpr("LLIf"), cond(cond), thenExpr(thenExpr), elseExpr(elseExpr) {}

  virtual llvm::Value* codegen(CodegenPass* pass);
  LLVar*  getTestExpr() { return cond; }
  LLExpr* getThenExpr() { return thenExpr; }
  LLExpr* getElseExpr() { return elseExpr; }
};

struct LLUntil : public LLExpr {
  LLExpr* cond; LLExpr* body;
  LLUntil(LLExpr* testExpr, LLExpr* thenExpr)
        : LLExpr("LLUntil"), cond(testExpr), body(thenExpr) {}

  virtual llvm::Value* codegen(CodegenPass* pass);
  LLExpr*& getTestExpr() { return cond; }
  LLExpr*& getThenExpr() { return body; }
};

struct DecisionTree;
struct LLCase : public LLExpr {
  LLVar* scrutinee;
  DecisionTree* dt;
  TypeAST* branchType;

  LLCase(LLVar* testExpr, DecisionTree* dt, TypeAST* ty)
    : LLExpr("LLCase"), scrutinee(testExpr), dt(dt), branchType(ty) {
  }

  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLAlloc : public LLExpr {
  LLVar* base;
  explicit LLAlloc(LLVar* e) : LLExpr("LLAlloc"), base(e) {}
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

typedef std::pair<string, int> CtorId;
struct DecisionTree;

struct Occurrence {
  std::vector<int> offsets;
};

struct SwitchCase {
  std::vector<CtorId>        ctors;
  std::vector<DecisionTree*> trees;
  DecisionTree*        defaultCase;
  Occurrence*                  occ;
  void codegen(CodegenPass* pass, llvm::Value* scrutinee, llvm::AllocaInst* rv_slot);
};

typedef std::pair<std::string, Occurrence*> DTBinding;
struct DecisionTree {
  enum Tag {
    DT_FAIL, DT_LEAF, DT_SWAP, DT_SWITCH
  } tag;
  TypeAST* type;
  std::vector<DTBinding> binds; LLExpr* action;
  SwitchCase* sc;
  DecisionTree(Tag t)            : tag(t), type(NULL), action(NULL), sc(NULL) {}
  DecisionTree(Tag t, std::vector<DTBinding> binds, LLExpr* e)
                                 : tag(t), type(NULL), binds(binds),
                                           action(e), sc(NULL) {}
  DecisionTree(Tag t, SwitchCase* sc)
                                 : tag(t), type(NULL), action(NULL), sc(sc) {}
  void codegen(CodegenPass* pass, llvm::Value* scrutinee, llvm::AllocaInst* rv_slot);
};

#endif // header guard

