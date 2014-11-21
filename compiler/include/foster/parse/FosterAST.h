// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "base/Assert.h"
#include "base/InputFile.h"
#include "base/Diagnostics.h"
#include "parse/FosterKindAST.h"

#include <vector>
#include <string>
#include <map>

#include "city.h"

#include "antlr3interfaces.h"

using std::string;

namespace llvm {
  class Type;
  class Value;
  class APInt;
  class ConstantInt;
}

using llvm::Type;
using llvm::APInt;

struct ExprAST;
struct VariableAST;
class  TypeAST;

struct DumpToProtobufPass;

typedef std::vector<ExprAST*> Exprs;

namespace foster {
  SourceRangeHighlighter show(ExprAST* ast);
  extern char kDefaultFnLiteralCallingConvention[];
}

///////////////////////////////////////////////////////////

struct ExprAST {
  std::vector<ExprAST*> parts;

  TypeAST* type;
  foster::SourceRange sourceRange;
  const char* const tag;

  explicit ExprAST(const char* const tag,
                   foster::SourceRange sourceRange)
    : type(NULL),
      sourceRange(sourceRange), tag(tag) {}
  virtual ~ExprAST() {}
  virtual void dump(DumpToProtobufPass* pass) = 0;
};

struct IntAST;
struct RatAST;
struct BoolAST;
struct SeqAST;
struct IfExprAST;
struct VariableAST;

struct Decl; struct Defn; struct Data;
struct ModuleAST {
  std::string name;
  std::string hash;
  const foster::InputTextBuffer* buf;
  std::vector<Defn*> defn_parts;
  std::vector<Decl*> decl_parts;
  std::vector<Data*> data_parts;
  std::vector<pANTLR3_COMMON_TOKEN> hiddenTokens;

  explicit ModuleAST(const std::vector<Decl*>& decls,
                     const std::vector<Defn*>& defns,
                     const std::vector<Data*>& datas,
                     const std::string& name,
                     const std::string& hash)
  : name(name), hash(hash), buf(NULL),
    defn_parts(defns), decl_parts(decls), data_parts(datas) {}
};

struct WholeProgramAST {
  std::map<uint128, ModuleAST*> seen;
  std::vector<ModuleAST*> modules;

  explicit WholeProgramAST() {}

  int getModuleCount() { return modules.size(); }
  ModuleAST* getModuleAST(int x) { return modules[x]; }
};


struct IntAST : public ExprAST {
private:
  const string text;
public:
  explicit IntAST(const string& originalText,
              foster::SourceRange sourceRange)
        : ExprAST("IntAST", sourceRange), text(originalText) {}
  virtual void dump(DumpToProtobufPass* pass);

  std::string getOriginalText() const { return text; }
};

struct RatAST : public ExprAST {
private:
  const string text;
public:
  explicit RatAST(const string& originalText,
              foster::SourceRange sourceRange)
        : ExprAST("RatAST", sourceRange), text(originalText) {}
  virtual void dump(DumpToProtobufPass* pass);

  std::string getOriginalText() const { return text; }
};

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val, foster::SourceRange sourceRange)
    : ExprAST("BoolAST", sourceRange), boolValue(val == "True") {
      ASSERT(val == "True" || val == "False") << show(sourceRange);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

struct StringAST : public ExprAST {
  std::string stringValue;
  explicit StringAST(string val, foster::SourceRange sourceRange)
    : ExprAST("StringAST", sourceRange), stringValue(val) {}
  virtual void dump(DumpToProtobufPass* pass);
};

struct VariableAST : public ExprAST {
private:
  string name;

public:
  explicit VariableAST(const string& name, TypeAST* aType,
                       foster::SourceRange sourceRange)
      : ExprAST("VariableAST", sourceRange), name(name) {
    this->type = aType;
  }

  virtual void dump(DumpToProtobufPass* pass);

  const string getName() const { return name; }
};

// base(args)
struct CallAST : public ExprAST {
  CallAST(ExprAST* base, Exprs args, foster::SourceRange sourceRange)
      : ExprAST("CallAST", sourceRange) {
    parts.push_back(base);
    for (size_t i = 0; i < args.size(); ++i) parts.push_back(args[i]);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

// 'prim' id :[types]? args
struct CallPrimAST : public ExprAST {
  std::string primname;
  std::vector<TypeAST*> types;

  CallPrimAST(std::string primname, Exprs args, std::vector<TypeAST*> types,
              foster::SourceRange sourceRange)
      : ExprAST("CallPrimAST", sourceRange), primname(primname), types(types) {
    for (size_t i = 0; i < args.size(); ++i) parts.push_back(args[i]);
  }
  virtual void dump(DumpToProtobufPass* pass);
  static CallPrimAST* one(const char* nm, ExprAST* e, foster::SourceRange sr) {
    std::vector<TypeAST*> _types;
    Exprs args; args.push_back(e);
    return new CallPrimAST(nm, args, _types, sr);
  }
  static CallPrimAST* two(const char* nm, ExprAST* e1, ExprAST* e2,
                          foster::SourceRange sr) {
    std::vector<TypeAST*> _types;
    Exprs args; args.push_back(e1); args.push_back(e2);
    return new CallPrimAST(nm, args, _types, sr);
  }
};

// e[ty]
struct ETypeAppAST : public ExprAST {
  std::vector<TypeAST*> typeArgs;
  explicit ETypeAppAST(TypeAST* overallType, ExprAST* base,
                       const std::vector<TypeAST*>& args,
                       foster::SourceRange sourceRange)
      : ExprAST("ETypeAppAST", sourceRange), typeArgs(args) {
    parts.push_back(base);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

// (e as ty)
struct ETypeCheckAST : public ExprAST {
  explicit ETypeCheckAST(ExprAST* base, TypeAST* checkedTy,
                         foster::SourceRange sourceRange)
      : ExprAST("ETypeCheckAST", sourceRange) {
    parts.push_back(base);
    this->type = checkedTy;
  }
  virtual void dump(DumpToProtobufPass* pass);
};


struct Binding {
  string name;
  ExprAST* body;
  explicit Binding(const string& name, ExprAST* body)
  : name(name), body(body) {}
};

struct LetAST : public ExprAST {
  std::vector<Binding> bindings;
  bool isRecursive;
  explicit LetAST(std::vector<Binding> bindings,
                  ExprAST* inexpr, bool rec,
                  foster::SourceRange sourceRange)
    : ExprAST("LetAST", sourceRange),
      bindings(bindings), isRecursive(rec) {
    parts.push_back(inexpr);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

struct SeqAST : public ExprAST {
  explicit SeqAST(Exprs exprs, foster::SourceRange sourceRange)
    : ExprAST("SeqAST", sourceRange) { this->parts = exprs; }
  virtual void dump(DumpToProtobufPass* pass);
};

//////////////////////////////////////////////
//////////////////////////////////////////////

struct Formal {
  string name; // eventually, pattern
  TypeAST* type;
  explicit Formal(const string& name, TypeAST* type)
  : name(name), type(type) {}
};

struct ValAbs : public ExprAST {
  std::vector<Formal> formals;
  std::vector<TypeFormal> tyVarFormals;
  TypeAST* resultType;
  string name;
  explicit ValAbs(std::vector<Formal> formals,
                  std::vector<TypeFormal> tyformals,
                  ExprAST* body,
                  TypeAST* resultType,
                  foster::SourceRange sourceRange)
  : ExprAST("ValAbs", sourceRange), formals(formals), tyVarFormals(tyformals),
    resultType(resultType) {
     parts.push_back(body);
  }

  virtual void dump(DumpToProtobufPass* pass);

  ExprAST*& getBody() { return parts[0]; }
};

// As noted by the designers of Lua, closures are an implementation strategy
// for the language feature of first-class function values.
//
// Some functions in Foster (such as those defined at the top level) are
// codegenned as plain C-like procedures, with signatures just as given.
//
// Others, like function literals that are immediately called, can be
// transformed to a C-like procedures with an augmented argument list
// (for the calling context to provide the variables that the called
//  function closes over).
//
// Other function literals are implemented as closures: a pair of
// pointer-to-procedure and generically-typed pointer-to-environment.
// The procedure's first argument is a pointer to its captured environment.
//
// At the typechecking level, a closure has function type, but at codegen time,
// its "external" LLVM type is a struct of function-taking-generic-env-ptr and
// generic-env-ptr. This allows type checking to be agnostic of the types stored
// in the env, while still allowing codegen to insert the appropriate bitcasts.

struct Defn {
  string name;
  ExprAST* body;
  explicit Defn(const string& name, ExprAST* body)
  : name(name), body(body) {}
};

struct Decl {
  string name;
  TypeAST* type;
  explicit Decl(const string& name, TypeAST* type)
  : name(name), type(type) {}
};

struct DataCtorAST {
  string name;
  std::vector<TypeAST*> types;
  foster::SourceRange sourceRange;
  explicit DataCtorAST(const string& name,
                       std::vector<TypeAST*> types,
                       foster::SourceRange range)
  : name(name), types(types), sourceRange(range) {}
};

struct Data {
  TypeFormal name;
  std::vector<DataCtorAST*> ctors;
  std::vector<TypeFormal> tyformals;
  foster::SourceRange sourceRange;
  explicit Data(const TypeFormal name,
                 std::vector<TypeFormal> tyformals,
                 std::vector<DataCtorAST*> ctors,
                 foster::SourceRange range)
  : name(name), ctors(ctors), tyformals(tyformals), sourceRange(range) {}
};

struct IfExprAST : public ExprAST {
  IfExprAST(ExprAST* testExpr, ExprAST* thenExpr, ExprAST* elseExpr,
            foster::SourceRange sourceRange)
    : ExprAST("IfExprAST", sourceRange) {
    parts.push_back(testExpr);
    parts.push_back(thenExpr);
    parts.push_back(elseExpr);
  }
  virtual void dump(DumpToProtobufPass* pass);

  ExprAST*& getTestExpr() { ASSERT(parts.size() == 3); return parts[0]; }
  ExprAST*& getThenExpr() { ASSERT(parts.size() == 3); return parts[1]; }
  ExprAST*& getElseExpr() { ASSERT(parts.size() == 3); return parts[2]; }
};

struct BuiltinCompilesExprAST : public ExprAST {
  explicit BuiltinCompilesExprAST(ExprAST* expr, foster::SourceRange sourceRange)
     : ExprAST("CompilesExprAST", sourceRange) {
       parts.push_back(expr);
   }
  // Must manually visit children (for typechecking)
  // because we don't want to codegen our children!
  virtual void dump(DumpToProtobufPass* pass);
};


class Pattern {
protected:
  Pattern(foster::SourceRange range) : sourceRange(range) {}
public:
  foster::SourceRange sourceRange;
  virtual void dump(DumpToProtobufPass* pass) = 0;
};

struct LiteralPattern : public Pattern {
public:
  ExprAST* pattern;
  enum Variety { LP_VAR, LP_NUM, LP_BOOL } variety;
  explicit LiteralPattern(foster::SourceRange range,
                          Variety v,
                          ExprAST* pattern) : Pattern(range), pattern(pattern), variety(v) {}
  virtual void dump(DumpToProtobufPass* pass);
};

struct CtorPattern : public Pattern {
  std::string ctorName;
  std::vector<Pattern*> patterns;
  explicit CtorPattern(foster::SourceRange range,
                       std::string name,
                       std::vector<Pattern*> pats)
    : Pattern(range), ctorName(name), patterns(pats) {}
  virtual void dump(DumpToProtobufPass* pass);
};

struct TuplePattern : public Pattern {
  std::vector<Pattern*> patterns;
  explicit TuplePattern(foster::SourceRange range,
                        std::vector<Pattern*> patterns)
    : Pattern(range), patterns(patterns) {}
  virtual void dump(DumpToProtobufPass* pass);
};

struct WildcardPattern : public Pattern {
  WildcardPattern(foster::SourceRange range) : Pattern(range) {}
  virtual void dump(DumpToProtobufPass* pass);
};

struct CaseBranch {
  Pattern* pattern;
  ExprAST* guard;
  ExprAST* body;
  explicit CaseBranch(Pattern* pattern, ExprAST* guard, ExprAST* body) :
    pattern(pattern), guard(guard), body(body) {}
};

struct CaseExpr : public ExprAST {
  std::vector<CaseBranch*> branches;
  explicit CaseExpr(ExprAST* scrutinee,
                    const std::vector<CaseBranch*>& branches,
                    const foster::SourceRange& sourceRange)
    : ExprAST("CaseExpr", sourceRange), branches(branches) {
    parts.push_back(scrutinee);
  }

  virtual void dump(DumpToProtobufPass* pass);
};

#endif // header guard

