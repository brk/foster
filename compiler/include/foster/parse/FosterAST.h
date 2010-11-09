// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "base/FilteringIterator.h"
#include "parse/FosterSymbolTable.h"

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
using llvm::Value;
using llvm::APInt;

class ExprAST;
class TypeAST;
class VariableAST;
class ExprASTVisitor;

typedef std::vector<ExprAST*> Exprs;
std::ostream& operator<<(std::ostream& out, ExprAST& expr);

string str(ExprAST* expr);
string str(TypeAST* type);
string str(Value* value);

namespace foster {
  SourceRangeHighlighter show(ExprAST* ast);
  struct CFG;
}

// Returns the closest
uint64_t getSaturating(const llvm::ConstantInt* v);

inline bool isArithOp(const std::string& op) {
  return op == "+" || op == "-" || op == "/" || op == "*";
}

inline bool isCmpOp(const std::string& op) {
  return op == "<" || op == "<=" || op == ">" || op == ">="
      || op == "==" || op == "!=";
}

///////////////////////////////////////////////////////////

struct ExprAST {
  typedef foster::SymbolTable<ExprAST>::LexicalScope ScopeType;

  std::vector<ExprAST*> parts;

  llvm::Value* value;
  TypeAST* type;
  foster::SourceRange sourceRange;
  const char* const tag;

  explicit ExprAST(const char* const tag,
                   foster::SourceRange sourceRange)
    : value(NULL), type(NULL),
      sourceRange(sourceRange), tag(tag) {}
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) const;
  virtual void accept(ExprASTVisitor* visitor) = 0;
};

struct BinaryExprAST : public ExprAST {
  explicit BinaryExprAST(const char* const tag,
                         ExprAST* e1, ExprAST* e2,
                         foster::SourceRange sourceRange)
      : ExprAST(tag, sourceRange) {
    this->parts.push_back(e1);
    this->parts.push_back(e2);
  }
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
  const APInt* apint;
  const string text;
  const int base;
public:
  explicit IntAST(int activeBits,
                  const string& originalText,
                  const string& cleanText, int base,
                  foster::SourceRange sourceRange);
  virtual void accept(ExprASTVisitor* visitor);

  const llvm::APInt& getAPInt() const;
  std::string getOriginalText() const;
  int getBase() const { return base; }

  unsigned intSizeForNBits(unsigned n) const;
};

llvm::ConstantInt* getConstantInt(IntAST* n);

IntAST* literalIntAST(int lit, const foster::SourceRange& sourceRange);

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val, foster::SourceRange sourceRange)
    : ExprAST("BoolAST", sourceRange), boolValue(val == "true") {}
  virtual void accept(ExprASTVisitor* visitor);
};

struct VariableAST : public ExprAST {
  string name;
  PrototypeAST* lazilyInsertedPrototype;

  explicit VariableAST(const string& name, TypeAST* aType,
                       foster::SourceRange sourceRange)
      : ExprAST("VariableAST", sourceRange),
        name(name), lazilyInsertedPrototype(NULL) {
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
  bool isClosureEnvironment;

  explicit TupleExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : ExprAST("TupleExprAST", sourceRange),
      isClosureEnvironment(false) {
    parts.push_back(expr);
  }
  virtual void accept(ExprASTVisitor* visitor);
};

// base[index]
struct SubscriptAST : public BinaryExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index,
                        foster::SourceRange sourceRange)
    : BinaryExprAST("SubscriptAST", base, index, sourceRange) {}
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
   std::vector<foster::CFG*> cfgs;

   PrototypeAST* proto;
   ScopeType* scope;

   // For closures; requires calcualation of free variables.
   // Top-level functions (which are, by definition, not closures)
   // have this field unset either in ANTLRtoFosterAST or
   // during lambda lifting.
   Exprs* environmentParts;
   bool isClosure() const { return environmentParts != NULL; }
   void markAsClosure() {
     ASSERT(!environmentParts);
     environmentParts = new Exprs();
   }
   void removeClosureEnvironment() {
     delete environmentParts;
     environmentParts = NULL;
   }

   explicit FnAST(PrototypeAST* proto, ExprAST* body,
                  ExprAST::ScopeType* ascope,
                  foster::SourceRange sourceRange)
      : ExprAST("FnAST", sourceRange),
        proto(proto), scope(ascope),
        environmentParts(NULL) {
     parts.push_back(body);
   }

   virtual void accept(ExprASTVisitor* visitor);

  std::string& getName() { return getProto()->name; }
  std::string getName() const { return getProto()->getName(); }
  PrototypeAST* getProto() { return proto; }
  PrototypeAST* getProto() const { return proto; }
  ExprAST*& getBody() { return parts[0]; }
};

struct ModuleAST : public ExprAST {
  ExprAST::ScopeType* scope;

  typedef foster::dynamic_cast_filtering_iterator<ExprAST, FnAST>
          FnAST_iterator;
  FnAST_iterator fn_begin() {
    return FnAST_iterator(parts.begin(), parts.end());
  }
  FnAST_iterator fn_end() {
    return FnAST_iterator(parts.end()  , parts.end());
  }

  explicit ModuleAST(const std::vector<ExprAST*>& _parts,
                     const std::string& name,
                     ExprAST::ScopeType* parentScope,
                     foster::SourceRange sourceRange)
    : ExprAST("ModuleAST", sourceRange)
    , scope(parentScope->newNestedScope(name)) {
    this->parts = _parts;
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

// This class exists only as a placeholder for the env ptr in a closure struct,
// for LLVM to generate a null pointer.
// For all intents and purposes, it does not exist before the closure
// conversion pass runs
struct NilExprAST : public ExprAST {
  explicit NilExprAST(foster::SourceRange sourceRange)
     : ExprAST("NilExprAST", sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor);
};

struct BuiltinCompilesExprAST : public ExprAST {
  enum Status { kWouldCompile, kWouldNotCompile, kNotChecked } status;
  explicit BuiltinCompilesExprAST(ExprAST* expr, foster::SourceRange sourceRange)
     : ExprAST("CompilesExprAST", sourceRange), status(kNotChecked) {
       parts.push_back(expr);
   }
  // Must manually visit children (for typechecking) because we don't want to codegen our children!
  virtual void accept(ExprASTVisitor* visitor);
};


#endif // header guard

