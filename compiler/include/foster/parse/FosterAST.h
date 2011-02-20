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
class ExprASTVisitor;

typedef std::vector<ExprAST*> Exprs;

string str(const ExprAST* expr);

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
  virtual std::ostream& operator<<(std::ostream& out) const;
  virtual void accept(ExprASTVisitor* visitor) = 0;
};

class IntAST;
class BoolAST;
class SeqAST;
class TupleExprAST;
class SubscriptAST;
class FnAST;
class IfExprAST;
class PrototypeAST;
class VariableAST;

class ModuleAST;

struct IntAST : public ExprAST {
private:
  const string text;
public:
  explicit IntAST(const string& originalText,
                  foster::SourceRange sourceRange);
  virtual void accept(ExprASTVisitor* visitor);

  std::string getOriginalText() const;
};

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val, foster::SourceRange sourceRange)
    : ExprAST("BoolAST", sourceRange), boolValue(val == "true") {}
  virtual void accept(ExprASTVisitor* visitor);
};

struct VariableAST : public ExprAST {
  string name;

  explicit VariableAST(const string& name, TypeAST* aType,
                       foster::SourceRange sourceRange)
      : ExprAST("VariableAST", sourceRange), name(name) {
    this->type = aType;
  }

  virtual void accept(ExprASTVisitor* visitor);

  const string& getName() { return name; }
  const string getName() const { return name; }
};

// base(args)
struct CallAST : public ExprAST {
  CallAST(ExprAST* base, Exprs args, foster::SourceRange sourceRange)
      : ExprAST("CallAST", sourceRange) {
    parts.push_back(base);
    for (size_t i = 0; i < args.size(); ++i) parts.push_back(args[i]);
  }
  virtual void accept(ExprASTVisitor* visitor);
};

// e[ty]
struct ETypeAppAST : public ExprAST {
  TypeAST* typeArg;
  explicit ETypeAppAST(TypeAST* overallType, ExprAST* base, TypeAST* arg,
                    foster::SourceRange sourceRange)
      : ExprAST("ETypeAppAST", sourceRange), typeArg(arg) {
    parts.push_back(base);
  }
  virtual void accept(ExprASTVisitor* visitor);
};

// In some sense, this is a type abstraction that's forced to be a redex
// (in exactly the same way that 'let' is). Only, unlike 'let', we don't
// (yet) have a standalone type abstraction. Also, in contrast to 'let',
// the scope of the name bound to this AST node is implicit, not explicit.
// The name is visible in all subsequent sibling AST nodes under the same
// parent.
struct NamedTypeDeclAST : public ExprAST {
  std::string name;
  explicit NamedTypeDeclAST(std::string boundName, TypeAST* namedType,
                            foster::SourceRange sourceRange)
    : ExprAST("NamedTypeDeclAST", sourceRange),
      name(boundName) { this->type = namedType; }
  virtual void accept(ExprASTVisitor* visitor);
  virtual std::ostream& operator<<(std::ostream& out) const;
};

struct SeqAST : public ExprAST {
  explicit SeqAST(Exprs exprs, foster::SourceRange sourceRange)
    : ExprAST("SeqAST", sourceRange) { this->parts = exprs; }
  virtual void accept(ExprASTVisitor* visitor);
};

struct TupleExprAST : public ExprAST {
  explicit TupleExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : ExprAST("TupleExprAST", sourceRange) {
    parts.push_back(expr);
  }
  virtual void accept(ExprASTVisitor* visitor);
};

// base[index]
struct SubscriptAST : public ExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index,
                        foster::SourceRange sourceRange)
    : ExprAST("SubscriptAST", sourceRange) {
    this->parts.push_back(base);
    this->parts.push_back(index);
  }
  virtual void accept(ExprASTVisitor* visitor);
};

class FnAST;

// The ->value for a PrototypeAST node is a llvm::Function*
struct PrototypeAST : public ExprAST {
private:
  string name;
  friend class FnAST;
public:

  string getName() const { return name; }

  std::vector<VariableAST*> inArgs;
  TypeAST* resultTy;

  PrototypeAST(TypeAST* retTy, const string& name,
         const std::vector<VariableAST*>& inArgs,
         foster::SourceRange sourceRange);

  virtual void accept(ExprASTVisitor* visitor);
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
 struct FnAST : public ExprAST {
   PrototypeAST* proto;

   explicit FnAST(PrototypeAST* proto, ExprAST* body,
                  foster::SourceRange sourceRange)
      : ExprAST("FnAST", sourceRange),
        proto(proto) {
     parts.push_back(body);
   }

   virtual void accept(ExprASTVisitor* visitor);

  std::string getName() const { return getProto()->getName(); }
  PrototypeAST* getProto() const { return proto; }
  ExprAST*& getBody() { return parts[0]; }
};

struct ModuleAST : public ExprAST {
  std::string name;
  std::vector<FnAST*> fn_parts;
  typedef std::vector<FnAST*>::iterator FnAST_iterator;
  FnAST_iterator fn_begin() { return fn_parts.begin();}
  FnAST_iterator fn_end() { return fn_parts.end(); }

  explicit ModuleAST(const std::vector<ExprAST*>& _parts,
                     const std::string& name,
                     foster::SourceRange sourceRange)
    : ExprAST("ModuleAST", sourceRange), name(name) {

      for (int i = 0; i < _parts.size(); ++i) {
        if (FnAST* f = dynamic_cast<FnAST*>(_parts[i])) {
          fn_parts.push_back(f);
        }
        // parts contains all subexprs,
        // some of which are copied in fn_parts.
        parts.push_back(_parts[i]);
      }
  }

  virtual void accept(ExprASTVisitor* visitor);
};

struct IfExprAST : public ExprAST {
  IfExprAST(ExprAST* testExpr, ExprAST* thenExpr, ExprAST* elseExpr,
            foster::SourceRange sourceRange)
    : ExprAST("IfExprAST", sourceRange) {
    parts.push_back(testExpr);
    parts.push_back(thenExpr);
    parts.push_back(elseExpr);
  }
  virtual void accept(ExprASTVisitor* visitor);

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
  virtual void accept(ExprASTVisitor* visitor);
};


#endif // header guard

