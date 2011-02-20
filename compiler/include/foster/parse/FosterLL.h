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
  typedef foster::SymbolTable<LLExpr>::LexicalScope ScopeType;

  TypeAST* type;
  foster::SourceRange sourceRange;
  const char* const tag;

  explicit LLExpr(const char* const tag,
                   foster::SourceRange sourceRange)
    : type(NULL), sourceRange(sourceRange), tag(tag) {}
  virtual ~LLExpr() {}

  virtual llvm::Value* codegen(CodegenPass* pass) = 0;
};

class LLInt;
class LLBool;
class LLTuple;
class LLSubscript;
class LLProc;
class LLIf;
class LLProto;


struct LLModule {
  const std::string name;
  std::vector<LLProc*> procs;
  std::vector<LLProto*> protos;

  explicit LLModule(const std::string& name,
                    const std::vector<LLProc*>& procs,
                    const std::vector<LLProto*>& protos)
  : name(name), procs(procs), protos(protos) {}

  void codegen(CodegenPass* pass);
};


// The ->value for a LLProto node is a llvm::Function*
struct LLProto {
private:
  FnTypeAST* type;
  string name;
  friend class LLProc;
public:
  llvm::Value* value;

  FnTypeAST* getFnType() { return type; }

  std::vector<std::string> argnames;

  LLProto(FnTypeAST* procType, const string& name,
          const std::vector<std::string>& argnames)
   : name(name), type(procType), argnames(argnames) {
    value = NULL;
  }
  const std::string& getName() const { return name; }
  virtual llvm::Value* codegen(CodegenPass* pass);
};


struct LLProc {
   LLProto* proto;
   LLExpr* body;

   explicit LLProc(LLProto* proto, LLExpr* body)
    : proto(proto), body(body) {}

  const std::string& getName() const { return proto->name; }
  LLProto* getProto() { return proto; }
  LLProto* getProto() const { return proto; }
  LLExpr*& getBody() { return body; }
  virtual llvm::Value* codegen(CodegenPass* pass);
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
    : LLExpr("LLInt", foster::SourceRange::getEmptyRange()) {
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
  explicit LLBool(string val, foster::SourceRange sourceRange)
    : LLExpr("LLBool", sourceRange), boolValue(val == "true") {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLVar : public LLExpr {
  string name;
  LLProto* lazilyInsertedPrototype;
  // Type is not used

  explicit LLVar(const string& name,
                 foster::SourceRange sourceRange)
      : LLExpr("LLVar", sourceRange),
        name(name), lazilyInsertedPrototype(NULL) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
  const string& getName() { return name; }
  const string getName() const { return name; }
};

// base(args)
struct LLCall : public LLExpr {
  LLVar* base;
  std::vector<LLVar*> args;
  LLCall(LLVar* base, std::vector<LLVar*>& args,
         foster::SourceRange sourceRange)
  : LLExpr("LLCall", sourceRange), base(base), args(args) { }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// e[ty]
struct LLTypeApp : public LLExpr {
  LLExpr* base;
  TypeAST* typeArg;
  explicit LLTypeApp(LLExpr* base, TypeAST* arg,
                    foster::SourceRange sourceRange)
      : LLExpr("LLTypeApp", sourceRange), base(base), typeArg(arg) {
  }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLTuple : public LLExpr {
  std::vector<LLExpr*> parts;
  bool isClosureEnvironment;
  explicit LLTuple(const std::vector<LLExpr*>& exprs, foster::SourceRange sourceRange)
    : LLExpr("LLTuple", sourceRange),
      isClosureEnvironment(false) {
    parts = exprs;
  }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

// base[index]
struct LLSubscript : public LLExpr {
  LLExpr* base;
  LLExpr* index;
  explicit LLSubscript(LLExpr* base, LLExpr* index,
                        foster::SourceRange sourceRange)
    : LLExpr("LLSubscript", sourceRange), base(base), index(index) {
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
  explicit LLClosures(LLExpr* expr, std::vector<LLClosure*>& closures,
                  foster::SourceRange sourceRange)
    : LLExpr("LLCLosures", sourceRange), expr(expr) { this->closures = closures; }
  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLLetVal : public LLExpr {
  std::string name;
  LLExpr* boundexpr;
  LLExpr* inexpr;
  explicit LLLetVal(const std::string& name,
                    LLExpr* boundexpr, LLExpr* inexpr)
  : LLExpr("LLLetVal", sourceRange),
     name(name), boundexpr(boundexpr), inexpr(inexpr) {}

  virtual llvm::Value* codegen(CodegenPass* pass);
};

struct LLIf : public LLExpr {
  std::vector<LLExpr*> parts;
  LLIf(LLExpr* testExpr, LLExpr* thenExpr, LLExpr* elseExpr,
            foster::SourceRange sourceRange)
    : LLExpr("LLIf", sourceRange) {
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
     : LLExpr("LLNil", sourceRange) {}
  virtual llvm::Value* codegen(CodegenPass* pass);
};

/*
struct RawPtrAST : public LLExpr {
  explicit RawPtrAST(Exprs exprs, foster::SourceRange sourceRange)
    : RawPtrAST("RawPtrAST", sourceRange) { this->parts = exprs; }

};
*/

#endif // header guard

