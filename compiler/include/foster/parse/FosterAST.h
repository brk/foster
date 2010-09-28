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
class PrototypeAST;
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
uint64_t getSaturating(llvm::Value* v);

bool isPrintRef(const ExprAST* base);

inline bool isArithOp(const std::string& op) {
  return op == "+" || op == "-" || op == "/" || op == "*";
}

inline bool isCmpOp(const std::string& op) {
  return op == "<" || op == "<=" || op == ">" || op == ">="
      || op == "==" || op == "!=";
}

///////////////////////////////////////////////////////////

struct ExprAST : public foster::NameResolver<ExprAST> {
  typedef foster::SymbolTable<foster::SymbolInfo>::LexicalScope ScopeType;

  ExprAST* parent;
  std::vector<ExprAST*> parts;

  llvm::Value* value;
  TypeAST* type;
  foster::SourceRange sourceRange;
  const char* const tag;

  explicit ExprAST(const char* const tag,
                   foster::SourceRange sourceRange, ExprAST* parent = NULL)
    : parent(parent), value(NULL), type(NULL),
      sourceRange(sourceRange), tag(tag) {}
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) const;
  virtual void accept(ExprASTVisitor* visitor) = 0;
  virtual ExprAST* lookup(const string& name, const string& meta) {
    ASSERT(false) << "ExprAST.lookup() called!";
    return NULL;
  }
};

struct UnaryExprAST : public ExprAST {
  explicit UnaryExprAST(const char* const tag,
                        ExprAST* e1, foster::SourceRange sourceRange)
    : ExprAST(tag, sourceRange) { this->parts.push_back(e1); }
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

// "Fake" AST node for doing iterative lookup.
struct NamespaceAST : public ExprAST {
  ExprAST::ScopeType* scope;

  explicit NamespaceAST(const char* const tag,
                        const std::string& name,
                        ExprAST::ScopeType* parentScope,
                        foster::SourceRange sourceRange)
      : ExprAST(tag, sourceRange),
        scope(parentScope->newNestedScope(name)) {
  }
  virtual ~NamespaceAST() { }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(NamespaceAST " << scope->getName() << ")";
  }
  virtual void accept(ExprASTVisitor* visitor);

  NamespaceAST* newNamespace(const std::string& name) {
    NamespaceAST* nu = new NamespaceAST("NamespaceAST", name, scope,
        foster::SourceRange::getEmptyRange());
    scope->insert(name, new foster::SymbolInfo(nu));
    return nu;
  }

  virtual ExprAST* lookup(const string& name, const string& meta) {
    foster::SymbolInfo* info = scope->lookup(name, meta);
    return info ? info->ast : NULL;
  }

  // TODO add wrapper to distinguish qualified from unqualified strings
  virtual ExprAST* insert(const string& fullyQualifiedName, VariableAST* var) {
    foster::SymbolInfo* info = scope->insert(fullyQualifiedName,
                                 new foster::SymbolInfo((ExprAST*)var));
    return info ? info->ast : NULL;
  }
};

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
  bool noInitialType;
  bool noFixedType() { return noInitialType && !type; }

  explicit VariableAST(const string& name, TypeAST* aType,
                       foster::SourceRange sourceRange)
      : ExprAST("VariableAST", sourceRange),
        name(name), lazilyInsertedPrototype(NULL) {
    this->type = aType;
    noInitialType = (aType == NULL);
  }

  virtual ExprAST* lookup(const string& name, const string& meta);

  virtual void accept(ExprASTVisitor* visitor);

  const string& getName() { return name; }
  const string getName() const { return name; }
};

struct UnaryOpExprAST : public UnaryExprAST {
  string op;
  explicit UnaryOpExprAST(string op, ExprAST* body, foster::SourceRange sourceRange)
     : UnaryExprAST("UnaryOp", body, sourceRange), op(op) {}
  virtual void accept(ExprASTVisitor* visitor);
};

struct BinaryOpExprAST : public BinaryExprAST {
  string op;
  enum { kLHS, kRHS };
  explicit BinaryOpExprAST(string op, ExprAST* lhs, ExprAST* rhs,
                           foster::SourceRange sourceRange)
     : BinaryExprAST("BinaryOp", lhs, rhs, sourceRange), op(op) {}
  virtual void accept(ExprASTVisitor* visitor);
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

struct TupleExprAST : public UnaryExprAST {
  bool isClosureEnvironment;

  explicit TupleExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST("TupleExprAST", expr, sourceRange) {
  }
  virtual void accept(ExprASTVisitor* visitor);
};

#if 0
struct ArrayExprAST : public UnaryExprAST {
  explicit ArrayExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor);
};
#endif

/*
struct SimdVectorAST : public UnaryExprAST {
  // Implicitly, a SeqAST
  explicit SimdVectorAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST("SimdVectorAST", expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor);
  virtual std::ostream& operator<<(std::ostream& out) const;
};
*/

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

  foster::SymbolTable<foster::SymbolInfo>::LexicalScope* scope;

  PrototypeAST(TypeAST* retTy, const string& name,
         const std::vector<VariableAST*>& inArgs,
         foster::SourceRange sourceRange,
         foster::SymbolTable<foster::SymbolInfo>::LexicalScope* ascope = NULL);

  virtual void accept(ExprASTVisitor* visitor);
};

// Closures are an implementation strategy for language feature
// of first-class function values.
//
// A closure stores a typed function pointer and a typed environment pointer.
// At the typechecking level, its type is a function type, but at the codegen level,
// its "external" LLVM type is a struct of function-taking-generic-env-ptr and
// generic-env-ptr. This allows type checking to be agnostic of the types stored
// in the env, while still allowing codegen to insert the appropriate bitcasts.
 struct FnAST : public ExprAST {
   std::vector<foster::CFG*> cfgs;

  PrototypeAST* proto;

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
                  foster::SourceRange sourceRange)
      : ExprAST("FnAST", sourceRange),
        proto(proto), environmentParts(NULL) {
     parts.push_back(body);
   }

   virtual void accept(ExprASTVisitor* visitor);

  std::string& getName() { return getProto()->name; }
  std::string getName() const { return getProto()->getName(); }
  PrototypeAST* getProto() { return proto; }
  PrototypeAST* getProto() const { return proto; }
  ExprAST*& getBody() { return parts[0]; }
};

struct ModuleAST : public NamespaceAST {
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
      : NamespaceAST("ModuleAST", name, parentScope, sourceRange) {
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


struct RefExprAST : public UnaryExprAST {
  bool isIndirect_;
  explicit RefExprAST(ExprAST* expr, bool isIndirect,
                      foster::SourceRange sourceRange)
    : UnaryExprAST("RefExprAST", expr, sourceRange),
      isIndirect_(isIndirect) {}
  virtual void accept(ExprASTVisitor* visitor);

  // Returns true if the physical representation of this reference
  // is T** instead of a simple T*.
  virtual bool isIndirect(); // TODO remove, along with inAssignLHS?
};

struct DerefExprAST : public UnaryExprAST {
  explicit DerefExprAST(ExprAST* expr, foster::SourceRange sourceRange)
     : UnaryExprAST("DerefExprAST", expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor);
};

struct AssignExprAST : public BinaryExprAST {
  explicit AssignExprAST(ExprAST* lhs, ExprAST* rhs, foster::SourceRange sourceRange)
     : BinaryExprAST("AssignExprAST", lhs, rhs, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor);
};

struct BuiltinCompilesExprAST : public UnaryExprAST {
  enum Status { kWouldCompile, kWouldNotCompile, kNotChecked } status;
  explicit BuiltinCompilesExprAST(ExprAST* expr, foster::SourceRange sourceRange)
     : UnaryExprAST("CompilesExprAST", expr, sourceRange), status(kNotChecked) {}
  // Must manually visit children (for typechecking) because we don't want to codegen our children!
  virtual void accept(ExprASTVisitor* visitor);
};


#endif // header guard

