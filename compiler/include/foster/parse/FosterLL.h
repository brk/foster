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
  // This must be a Var instead of just a string
  LLVar* base; // because
  std::vector<LLVar*> args;
  LLCall(LLVar* base, std::vector<LLVar*>& args)
  : LLExpr("LLCall"), base(base), args(args) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLTuple : public LLExpr {
  std::vector<LLExpr*> parts;
  bool isClosureEnvironment;
  explicit LLTuple(const std::vector<LLExpr*>& exprs)
    : LLExpr("LLTuple"),
      isClosureEnvironment(false) {
    parts = exprs;
  }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// base[index]
struct LLSubscript : public LLExpr {
  LLExpr* base;
  LLExpr* index;
  explicit LLSubscript(LLExpr* base, LLExpr* index)
    : LLExpr("LLSubscript"), base(base), index(index) {
    }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLClosure {
  std::string varname;
  std::string procname;
  std::vector<std::string> vars;
  explicit LLClosure(const std::string& varname,
                     const std::string& procname,
                     const std::vector<std::string>& vars)
    : varname(varname), procname(procname), vars(vars) {}
 virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLClosures : public LLExpr {
  LLExpr* expr;
  std::vector<LLClosure*> closures;
  explicit LLClosures(LLExpr* expr, std::vector<LLClosure*>& closures)
    : LLExpr("LLCLosures"), expr(expr) { this->closures = closures; }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLLetVal : public LLExpr {
  std::string name;
  LLExpr* boundexpr;
  LLExpr* inexpr;
  explicit LLLetVal(const std::string& name,
                    LLExpr* boundexpr, LLExpr* inexpr)
  : LLExpr("LLLetVal"),
     name(name), boundexpr(boundexpr), inexpr(inexpr) {}

  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLIf : public LLExpr {
  std::vector<LLExpr*> parts;
  LLIf(LLExpr* testExpr, LLExpr* thenExpr, LLExpr* elseExpr)
    : LLExpr("LLIf") {
    parts.push_back(testExpr);
    parts.push_back(thenExpr);
    parts.push_back(elseExpr);
  }

  virtual llvm::Value* codegen(CodegenPass* pass);
  LLExpr*& getTestExpr() { ASSERT(parts.size() == 3); return parts[0]; }
  LLExpr*& getThenExpr() { ASSERT(parts.size() == 3); return parts[1]; }
  LLExpr*& getElseExpr() { ASSERT(parts.size() == 3); return parts[2]; }
};

struct LLNil : public LLExpr {
  explicit LLNil(foster::SourceRange sourceRange)
     : LLExpr("LLNil") {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLAlloc : public LLExpr {
  LLExpr* base;
  explicit LLAlloc(LLExpr* e) : LLExpr("LLAlloc"), base(e) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLDeref : public LLExpr {
  LLExpr* base;
  explicit LLDeref(LLExpr* e) : LLExpr("LLDeref"), base(e) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLStore : public LLExpr {
  LLExpr* v; LLExpr* r;
  explicit LLStore(LLExpr* v, LLExpr* r)
    : LLExpr("LLStore"), v(v), r(r) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

/*
struct RawPtrAST : public LLExpr {
  explicit RawPtrAST(Exprs exprs)
    : RawPtrAST("RawPtrAST") { this->parts = exprs; }

};
*/

struct LLCoroPrim : public LLExpr {
  string   primName;
  TypeAST* retType;
  TypeAST* typeArg;
  explicit LLCoroPrim(string primName, TypeAST* ret, TypeAST* arg)
      : LLExpr("LLCoroPrim"), primName(primName),
        retType(ret), typeArg(arg) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

#endif // header guard

