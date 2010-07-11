// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "llvm/LLVMContext.h"
#include "llvm/DerivedTypes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Constants.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

#include "base/Assert.h"
#include "base/InputFile.h"
#include "base/Diagnostics.h"
#include "parse/FosterASTVisitor.h"
#include "parse/FosterTypeAST.h"

#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <cstdio>
#include <sstream>

using std::string;
using std::endl;

using llvm::Type;
using llvm::Module;
using llvm::Value;
using llvm::getGlobalContext;
using llvm::APInt;
using llvm::Function;

std::ostream& operator <<(std::ostream& out, const foster::SourceRange& r);

class ExprAST; // fwd decl
class TypeAST; // fwd decl

typedef std::vector<ExprAST*> Exprs;
std::ostream& operator<<(std::ostream& out, ExprAST& expr);

void fosterInitializeLLVM();

string freshName(string like);

extern llvm::ExecutionEngine* ee;
extern llvm::IRBuilder<> builder;
extern Module* module;

string join(string glue, Exprs args);
string str(ExprAST* expr);
string str(TypeAST* type);
string str(Value* value);
namespace foster {
SourceRangeHighlighter show(ExprAST* ast);
}

TypeAST* TypeASTFor(const string& name);
const Type* LLVMTypeFor(const string& name);
void initModuleTypeNames();

inline bool isSmallPowerOfTwo(int x) {
  return (x == 2) || (x == 4) || (x == 8) || (x == 16);
}

template <typename T>
T getSaturating(llvm::Value* v) {
  // If the value requires more bits than T can represent, we want
  // to return ~0, not 0. Otherwise, we should leave the value alone.
  T allOnes = ~T(0);
  if (!v) {
    std::cerr << "numericOf() got a null value, returning " << allOnes << std::endl;
    return allOnes;
  }

  if (llvm::ConstantInt* ci = llvm::dyn_cast<llvm::ConstantInt>(v)) {
    return static_cast<T>(ci->getLimitedValue(allOnes));
  } else {
    llvm::errs() << "numericOf() got a non-constant-int value " << *v << ", returning " << allOnes << "\n";
    return allOnes;
  }
}

///////////////////////////////////////////////////////////

template <typename T>
struct NameResolver {
  virtual T* lookup(const string& name, const string& meta) = 0;
  virtual ~NameResolver() {}
};

struct ExprAST : public NameResolver<ExprAST> {
  ExprAST* parent;
  std::vector<ExprAST*> parts;

  llvm::Value* value;
  TypeAST* type;
  foster::SourceRange sourceRange;

  explicit ExprAST(foster::SourceRange sourceRange, ExprAST* parent = NULL)
    : parent(parent), value(NULL), type(NULL), sourceRange(sourceRange) {}
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) const = 0;
  virtual void accept(FosterASTVisitor* visitor) = 0;
  virtual ExprAST* lookup(const string& name, const string& meta) {
    std::cerr << "ExprAST.lookup() called!" << std::endl;
    return NULL;
  }
};

struct UnaryExprAST : public ExprAST {
  explicit UnaryExprAST(ExprAST* e1, foster::SourceRange sourceRange)
    : ExprAST(sourceRange) { this->parts.push_back(e1); }
};

struct BinaryExprAST : public ExprAST {
  explicit BinaryExprAST(ExprAST* e1, ExprAST* e2,
      foster::SourceRange sourceRange) : ExprAST(sourceRange) {
    this->parts.push_back(e1);
    this->parts.push_back(e2);
  }
};

// Implements persistent lexical scopes using a cactus stack arrangement
template <typename T>
class FosterSymbolTable : public NameResolver<T> {
public:
  class LexicalScope : public NameResolver<T> {
    string name;
    typedef std::map<string, T*> Map;
    Map val_of;
  public:
    LexicalScope* parent;
    
    LexicalScope(string name, LexicalScope* parent) : name(name), parent(parent) {}
    virtual ~LexicalScope() {}
    
    T* insert(const string& ident, T* V) { val_of[ident] = V; return V; }
    T* lookup(const string& ident, const string& wantedScopeName) {
      if (name == "*" || wantedScopeName == "" || name == wantedScopeName) {
        typename Map::iterator it = val_of.find(ident);
        if (it != val_of.end()) {
          return (*it).second;
        }
      }
      if (parent) {
        return parent->lookup(ident, wantedScopeName);
      } else {
        return NULL;
      }
    }
    void dump(std::ostream& out) {
      out << "\t" << name << "(@ " << this << ")" << std::endl;
      for (typename Map::iterator it = val_of.begin(); it != val_of.end(); ++it) {
        out << "\t\t" << (*it).first << ": " << (*it).second << std::endl;
      }
      if (parent) { parent->dump(out); }
    }
  };

  FosterSymbolTable() {
    pushExistingScope(new LexicalScope("*", NULL));
  }
  virtual ~FosterSymbolTable() {}
  T* lookup(const string& ident, const string& wantedScopeName) {
    return currentScope()->lookup(ident, wantedScopeName);
  }
  T* insert(string ident, T* V) { return currentScope()->insert(ident, V); }
  LexicalScope* pushScope(string scopeName) {
    currentScope() = new LexicalScope(scopeName, currentScope());
    return currentScope();
  }
  LexicalScope* popScope() {
    currentScope() = currentScope()->parent;
    return currentScope();
  }

  void pushExistingScope(LexicalScope* scope) {
    scopeStack.push_back(scope);
  }
  void popExistingScope(LexicalScope* expectedCurrentScope) {
    ASSERT(currentScope() == expectedCurrentScope);
    scopeStack.pop_back();
  }

  void dump(std::ostream& out) { currentScope()->dump(out); }

  private:
  LexicalScope*& currentScope() { return scopeStack.back(); }
  std::vector<LexicalScope*> scopeStack;
};

// {{{ |scope| maps names (var/fn) to llvm::Value*/llvm::Function*
extern FosterSymbolTable<Value> scope;
extern FosterSymbolTable<TypeAST> typeScope;
extern FosterSymbolTable<ExprAST> varScope;
// }}}

// "Fake" AST node for doing iterative lookup; AST stand-in for namespaces.
struct NameResolverAST : public ExprAST {
  FosterSymbolTable<ExprAST> localScope;
  const std::string& scopeName;

  explicit NameResolverAST(const std::string& name)
      : ExprAST(foster::SourceRange::getEmptyRange()), scopeName(name) {
    localScope.pushScope(scopeName);
  }
  virtual ~NameResolverAST() { localScope.popScope(); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(NameResolver " << scopeName << ")";
  }
  virtual void accept(FosterASTVisitor* visitor) {
    std::cerr << "Visitor called on NameResolverAST! This is probably not desired..." << std::endl;
  }
  NameResolverAST* newNamespace(const std::string& name) {
    NameResolverAST* nu = new NameResolverAST(name);
    localScope.insert(name, nu);
    return nu;
  }
  virtual ExprAST* lookup(const string& name, const string& meta) {
    return localScope.lookup(name, meta);
  }
  virtual ExprAST* insert(const string& fullyQualifiedName, VariableAST* var) {
    return localScope.insert(fullyQualifiedName, (ExprAST*)(var));
  }
};

struct IntAST : public ExprAST {
  string Text; // The literal text from the source file; for example, "1010`1011`1101_2"
  string Clean; // The text without separator chars or base; for example, "101010111101"
  int Base; // The numeric base, if any, attached to the literal.
  explicit IntAST(string originalText, string valText,
                  foster::SourceRange sourceRange, int base = 10)
    : ExprAST(sourceRange), Text(originalText), Clean(valText), Base(base) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  llvm::Constant* getConstantValue();
  llvm::APInt getAPInt();

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "IntAST(" << Text << ")";
  }
};

IntAST* literalIntAST(int lit);

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val, foster::SourceRange sourceRange)
    : ExprAST(sourceRange), boolValue(val == "true") {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "BoolAST(" << string(boolValue ? "true" : "false") << ")";
  }
};

struct VariableAST : public ExprAST {
  string name;
  PrototypeAST* lazilyInsertedPrototype;
  bool noInitialType;
  bool noFixedType() { return noInitialType && !type; }

  // TODO need to figure out how/where/when to assign type info to nil
  explicit VariableAST(const string& name, TypeAST* aType,
                       foster::SourceRange sourceRange)
      : ExprAST(sourceRange), name(name), lazilyInsertedPrototype(NULL) {
    this->type = aType;
    noInitialType = (aType == NULL);
  }

  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (type) {
      return out << "VarAST( " << name << " : " << str(type) << ")";
    } else {
      return out << "VarAST( " << name << " : " << ")";
    }
  }
};

struct UnaryOpExprAST : public UnaryExprAST {
  string op;
  explicit UnaryOpExprAST(string op, ExprAST* body, foster::SourceRange sourceRange)
     : UnaryExprAST(body, sourceRange), op(op) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "UnaryOp(" << op << ' ' << str(this->parts[0]) << ")";
  }
};

struct BinaryOpExprAST : public BinaryExprAST {
  string op;
  enum { kLHS, kRHS };
  explicit BinaryOpExprAST(string op, ExprAST* lhs, ExprAST* rhs,
                           foster::SourceRange sourceRange)
     : BinaryExprAST(lhs, rhs, sourceRange), op(op) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    ExprAST* LHS = this->parts[kLHS];
    ExprAST* RHS = this->parts[kRHS];
    return out << "BinaryOp(lhs=" << str(LHS) << ", op=" << op << ", rhs="  << str(RHS) << ")";
  }
};

// base(args)
struct CallAST : public ExprAST {
  CallAST(ExprAST* base, Exprs args, foster::SourceRange sourceRange)
      : ExprAST(sourceRange) {
    parts.push_back(base);
    for (size_t i = 0; i < args.size(); ++i) parts.push_back(args[i]);
  }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "CallAST(base = " << str(this->parts[0]) << ", args = ";
    for (size_t i = 1; i < this->parts.size(); ++i) {
      out << " " << str(this->parts[i]) << ", ";
    }
    return out << ")";
  }
};

struct SeqAST : public ExprAST {
  explicit SeqAST(Exprs exprs, foster::SourceRange sourceRange)
    : ExprAST(sourceRange) { this->parts = exprs; }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "SeqAST { ";
    for (size_t i = 0; i < this->parts.size(); ++i) {
      if (i > 0) out << " ;\n";
      out << str(this->parts[i]);
    }
    return out << " }";
  }
};

struct TupleExprAST : public UnaryExprAST {
  bool isClosureEnvironment;
  std::string typeName;

  explicit TupleExprAST(ExprAST* expr, const std::string& typeName,
                        foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange),
      isClosureEnvironment(false), typeName(typeName) { }

  explicit TupleExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange) {
    std::cout << "\t\t\tTupleExprAST " << expr << " ; " << this->parts[0] << std::endl;
  }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "TupleExpr(" << str(this->parts[0]) << ")";
  }
};

struct ArrayExprAST : public UnaryExprAST {
  explicit ArrayExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "ArrayExpr(" << str(this->parts[0]) << ")";
  }
};

struct SimdVectorAST : public UnaryExprAST {
  // Implicitly, a SeqAST
  explicit SimdVectorAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "SimdVector(" << str(this->parts[0]) << ")";
  }
};

// base[index]
struct SubscriptAST : public BinaryExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index,
                        foster::SourceRange sourceRange)
    : BinaryExprAST(base, index, sourceRange) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "SubscriptAST(base = " << str(this->parts[0]) << ", index = " << str(this->parts[1]) << ")";
  }
};

// The ->value for a PrototypeAST node is a llvm::Function*
struct PrototypeAST : public ExprAST {
  string name;
  std::vector<VariableAST*> inArgs;
  TypeAST* resultTy;

  FosterSymbolTable<ExprAST>::LexicalScope* scope;

  PrototypeAST(TypeAST* retTy, const string& name,
               foster::SourceRange sourceRange)
      : ExprAST(sourceRange), name(name), resultTy(retTy), scope(NULL) {
  }

  PrototypeAST(TypeAST* retTy, const string& name,
               const std::vector<VariableAST*>& inArgs,
               foster::SourceRange sourceRange)
      : ExprAST(sourceRange),
        name(name), inArgs(inArgs), resultTy(retTy), scope(NULL) {
    if (resultTy == NULL) {
      this->resultTy = TypeAST::get(LLVMTypeFor("i32"));
    } else {
      //std::cout << "\n\tProtoAST " << name << " ascribed result type of " << *(retTy) << std::endl;
    }
  }

  PrototypeAST(TypeAST* retTy, const string& name,
               const std::vector<VariableAST*>& inArgs,
               FosterSymbolTable<ExprAST>::LexicalScope* scope,
               foster::SourceRange sourceRange)
      : ExprAST(sourceRange),
        name(name), inArgs(inArgs), resultTy(retTy), scope(scope) {
    if (resultTy == NULL) {
      this->resultTy = TypeAST::get(LLVMTypeFor("i32"));
    } else {
      std::cout << "\n\tProtoAST " << name << " ascribed result type expr of " << str(retTy) << std::endl;
    }
  }

  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "PrototypeAST(name = " << name;
    for (size_t i = 0; i < inArgs.size(); ++i) {
      out << ", arg["<<i<<"] = " << str(inArgs[i]);
    }
    if (resultTy != NULL) {
      out << ", resultTy=" << str(resultTy);
    }
    out << ")";
    return out;
  }
};

struct FnAST : public ExprAST {
  PrototypeAST* proto;
  ExprAST* body;
  bool wasNested;
  bool lambdaLiftOnly;

  explicit FnAST(PrototypeAST* proto, ExprAST* body,
                 foster::SourceRange sourceRange)
    : ExprAST(sourceRange),
      proto(proto), body(body),
      wasNested(false), lambdaLiftOnly(false) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "FnAST(proto = " << str(proto) << ", body = " << str(body) << endl;
  }
};

// A closure stores a typed function pointer and a typed environment pointer.
// Its "external" type is a struct of function-taking-generic-env-ptr and
// generic-env-ptr. This allows type checking to be agnostic of the types stored
// in the env, while still allowing codegen to insert the appropriate bitcasts.
struct ClosureAST : public ExprAST {
  // Closures created for fn AST nodes during AST parsing will
  // wrap the function AST node, and will not initially have
  // known environment type exprs (which requires calculation of
  // free variables) in this->parts.
  FnAST* fn;

  // Closures created during closure conversion will get this flag
  // set at creation time; existing closures will set this flag
  // during closure conversion of the above fn AST node.
  bool hasKnownEnvironment;

  // LLVM supports generation of trampoline code, which allows us to pass
  // closure values to C code expecting a raw function pointer -- very cool.
  // LLVM generates different code for the trampoline and non-trampoline
  // versions of a given function. Due to a separate restriction in LLVM,
  // we must write closures "directly" at trampoline creation sites, which
  // implies we don't need to worry about generating both the trampoline
  // and non-trampoline versions of the closed fn.
  bool isTrampolineVersion;

  explicit ClosureAST(FnAST* fn, foster::SourceRange sourceRange)
    : ExprAST(sourceRange), fn(fn),
      hasKnownEnvironment(false), isTrampolineVersion(false) { }

  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (hasKnownEnvironment && fn) {
      out << "(closure " << str(fn->proto);
      for (size_t i = 0; i < parts.size(); ++i) {
        out << "\t" << str(parts[i]);
      }
      return out << ")";
    } else if (fn) {
      return out << "(unrefined closure " << str(fn->proto) << ")";
    } else {
      return out << "(malformed closure)";
    }
  }
};

struct IfExprAST : public ExprAST {
  ExprAST* testExpr, *thenExpr, *elseExpr;
  IfExprAST(ExprAST* testExpr, ExprAST* thenExpr, ExprAST* elseExpr,
            foster::SourceRange sourceRange)
    : ExprAST(sourceRange),
      testExpr(testExpr), thenExpr(thenExpr), elseExpr(elseExpr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "if (" << str(testExpr) << ")" <<
        " then " << str(thenExpr) << " else " << str(elseExpr);
  }
};

// for var in start to end { body }
struct ForRangeExprAST : public ExprAST {
  VariableAST* var;
  ExprAST* startExpr;
  ExprAST* endExpr;
  ExprAST* bodyExpr;
  ExprAST* incrExpr;

  explicit ForRangeExprAST(VariableAST* var,
		  ExprAST* start, ExprAST* end,
                  ExprAST* body, ExprAST* incr,
                  foster::SourceRange sourceRange)
    : ExprAST(sourceRange),
      var(var), startExpr(start), endExpr(end),
      bodyExpr(body), incrExpr(incr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "for " << var->name << " in " << str(startExpr) << " to " << str(endExpr);
    if (incrExpr) out  << " by " << str(incrExpr);
    out << " do " << str(bodyExpr);
    return out;
  }
};

struct NilExprAST : public ExprAST {
  explicit NilExprAST(foster::SourceRange sourceRange)
     : ExprAST(sourceRange) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "NilExprAST()";
  }
};

struct RefExprAST : public UnaryExprAST {
  bool isNullable;
  bool isIndirect_;
  explicit RefExprAST(ExprAST* expr, bool isNullable, bool isIndirect,
                      foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange),
      isNullable(isNullable), isIndirect_(isIndirect) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "RefExprAST(nullable?=" << isNullable << ", " << str(this->parts[0]) << ")";
  }

  // Returns true if the physical representation of this reference
  // is T** instead of a simple T*.
  virtual bool isIndirect();
};

struct DerefExprAST : public UnaryExprAST {
  explicit DerefExprAST(ExprAST* expr, foster::SourceRange sourceRange)
     : UnaryExprAST(expr, sourceRange) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "DerefExprAST(" << str(this->parts[0]) << ")";
  }
};

struct AssignExprAST : public BinaryExprAST {
  explicit AssignExprAST(ExprAST* lhs, ExprAST* rhs, foster::SourceRange sourceRange)
     : BinaryExprAST(lhs, rhs, sourceRange) {}
  virtual void accept(FosterASTVisitor* visitor) {
    visitor->inAssignLHS = true;
    parts[0]->accept(visitor);
    visitor->inAssignLHS = false;

    parts[1]->accept(visitor);
    visitor->visit(this);
  }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "AssignExprAST(lhs=" << str(this->parts[0])
        << ", rhs=" << str(parts[1]) << ")" << std::endl;
  }
};

struct BuiltinCompilesExprAST : public UnaryExprAST {
  enum Status { kWouldCompile, kWouldNotCompile, kNotChecked } status;
  explicit BuiltinCompilesExprAST(ExprAST* expr, foster::SourceRange sourceRange)
     : UnaryExprAST(expr, sourceRange), status(kNotChecked) {}
  // Must manually visit children (for typechecking) because we don't want to codegen our children!
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(__COMPILES__ " << str(this->parts[0]) << ")";
  }
};


#endif // header guard

