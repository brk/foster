// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include <vector>
#include <string>

using std::string;

namespace llvm {
  class Type;
  class Value;
  class APInt;
  class ConstantInt;
}

using llvm::Type;
using llvm::APInt;

class ExprAST;
class TypeAST;
class VariableAST;

class DumpToProtobufPass;

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

class IntAST;
class BoolAST;
class SeqAST;
class TupleExprAST;
class SubscriptAST;
class IfExprAST;
class VariableAST;

class Decl; class Defn;
struct ModuleAST {
  std::string name;
  const foster::InputTextBuffer* buf;
  std::vector<Defn*> defn_parts;
  std::vector<Decl*> decl_parts;

  explicit ModuleAST(const std::vector<Decl*>& decls,
                     const std::vector<Defn*>& defns,
                     const std::string& name)
  : name(name), buf(NULL), defn_parts(defns), decl_parts(decls) {}
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

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val, foster::SourceRange sourceRange)
    : ExprAST("BoolAST", sourceRange), boolValue(val == "true") {}
  virtual void dump(DumpToProtobufPass* pass);
};

struct VariableAST : public ExprAST {
  string name;

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

// e[ty]
struct ETypeAppAST : public ExprAST {
  TypeAST* typeArg;
  explicit ETypeAppAST(TypeAST* overallType, ExprAST* base, TypeAST* arg,
                    foster::SourceRange sourceRange)
      : ExprAST("ETypeAppAST", sourceRange), typeArg(arg) {
    parts.push_back(base);
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

struct TupleExprAST : public ExprAST {
  explicit TupleExprAST(Exprs exprs, foster::SourceRange sourceRange)
    : ExprAST("TupleExprAST", sourceRange) {
      for (size_t i = 0; i < exprs.size(); ++i) { parts.push_back(exprs[i]); }
  }
  virtual void dump(DumpToProtobufPass* pass);
};

//////////////////////////////////////////////
//////////////////////////////////////////////

// (ref base)
struct AllocAST : public ExprAST {
  explicit AllocAST(ExprAST* base,
                    foster::SourceRange sourceRange)
    : ExprAST("AllocAST", sourceRange) {
    this->parts.push_back(base);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

// base^
struct DerefAST : public ExprAST {
  explicit DerefAST(ExprAST* base,
                   foster::SourceRange sourceRange)
    : ExprAST("DerefAST", sourceRange) {
    this->parts.push_back(base);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

// ev >^ er
struct StoreAST : public ExprAST {
  explicit StoreAST(ExprAST* ev, ExprAST* er,
                    foster::SourceRange sourceRange)
    : ExprAST("StoreAST", sourceRange) {
    this->parts.push_back(ev);
    this->parts.push_back(er);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

//////////////////////////////////////////////
//////////////////////////////////////////////

// base[index]
struct SubscriptAST : public ExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index,
                        foster::SourceRange sourceRange)
    : ExprAST("SubscriptAST", sourceRange) {
    this->parts.push_back(base);
    this->parts.push_back(index);
  }
  virtual void dump(DumpToProtobufPass* pass);
};

struct Formal {
  string name; // eventually, pattern
  TypeAST* type;
  explicit Formal(const string& name, TypeAST* type)
  : name(name), type(type) {}
};

struct ValAbs : public ExprAST {
  std::vector<Formal*> formals;
  TypeAST* resultType;
  string name;
  explicit ValAbs(std::vector<Formal*> formals, ExprAST* body,
                  TypeAST* resultType, foster::SourceRange sourceRange)
  : ExprAST("ValAbs", sourceRange), formals(formals), resultType(resultType) {
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

struct UntilExpr : public ExprAST {
  UntilExpr(ExprAST* testExpr, ExprAST* thenExpr,
            foster::SourceRange sourceRange)
    : ExprAST("UntilExpr", sourceRange) {
    parts.push_back(testExpr);
    parts.push_back(thenExpr);
  }
  virtual void dump(DumpToProtobufPass* pass);

  ExprAST*& getTestExpr() { ASSERT(parts.size() == 2); return parts[0]; }
  ExprAST*& getThenExpr() { ASSERT(parts.size() == 2); return parts[1]; }
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
  enum Variety { LP_VAR, LP_INT, LP_BOOL } variety;
  explicit LiteralPattern(foster::SourceRange range,
                          Variety v,
                          ExprAST* pattern) : Pattern(range), pattern(pattern), variety(v) {}
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

typedef std::pair<Pattern*, ExprAST*> CaseBranch;
struct CaseExpr : public ExprAST {
  std::vector<CaseBranch> branches;
  explicit CaseExpr(ExprAST* scrutinee,
                    const std::vector<CaseBranch>& branches,
                    const foster::SourceRange& sourceRange)
    : ExprAST("CaseExpr", sourceRange), branches(branches) {
    parts.push_back(scrutinee);
  }

  virtual void dump(DumpToProtobufPass* pass);
};

#endif // header guard

