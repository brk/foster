// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "llvm/DerivedTypes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Constants.h"
#include "llvm/Support/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

#include "base/Assert.h"
#include "base/InputFile.h"
#include "base/Diagnostics.h"
#include "base/FilteringIterator.h"
#include "parse/ExprASTVisitor.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterSymbolTable.h"

#include "CompilationContext.h"

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
using llvm::APInt;
using llvm::Function;

class ExprAST; // fwd decl
class TypeAST; // fwd decl

typedef std::vector<ExprAST*> Exprs;
std::ostream& operator<<(std::ostream& out, ExprAST& expr);

string freshName(string like);

string str(ExprAST* expr);
string str(TypeAST* type);
string str(Value* value);

namespace foster {
  SourceRangeHighlighter show(ExprAST* ast);
  struct CFG;
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

struct ExprAST : public foster::NameResolver<ExprAST> {
  typedef foster::SymbolTable<foster::SymbolInfo>::LexicalScope ScopeType;

  ExprAST* parent;
  std::vector<ExprAST*> parts;

  llvm::Value* value;
  TypeAST* type;
  foster::SourceRange sourceRange;

  explicit ExprAST(foster::SourceRange sourceRange, ExprAST* parent = NULL)
    : parent(parent), value(NULL), type(NULL), sourceRange(sourceRange) {}
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) const = 0;
  virtual void accept(ExprASTVisitor* visitor) = 0;
  virtual ExprAST* lookup(const string& name, const string& meta) {
    ASSERT(false) << "ExprAST.lookup() called!";
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

// "Fake" AST node for doing iterative lookup.
struct NamespaceAST : public ExprAST {
  ExprAST::ScopeType* scope;

  explicit NamespaceAST(const std::string& name,
                           ExprAST::ScopeType* parentScope,
                           foster::SourceRange sourceRange)
      : ExprAST(sourceRange),
        scope(parentScope->newNestedScope(name)) {
  }
  virtual ~NamespaceAST() { }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(NamespaceAST " << scope->getName() << ")";
  }
  virtual void accept(ExprASTVisitor* visitor) {
    std::cerr << "Visitor called on NamespaceAST! This is probably not desired..." << std::endl;
  }

  NamespaceAST* newNamespace(const std::string& name) {
    NamespaceAST* nu = new NamespaceAST(name, scope,
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
                  foster::SourceRange sourceRange)
        : ExprAST(sourceRange), text(originalText), base(base) {
    // Debug builds of LLVM don't ignore leading zeroes when considering
    // needed bit widths.
    int bitsLLVMneeds = (std::max)(intSizeForNBits(activeBits),
                                   (unsigned) cleanText.size());
    int ourSize = intSizeForNBits(bitsLLVMneeds);
    apint = new APInt(ourSize, cleanText, base);
    type = TypeAST::i(ourSize);
  }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }

  llvm::Constant* getConstantValue() const;
  llvm::APInt getAPInt() const;
  std::string getOriginalText() const;
  int getBase() const { return base; }
  
  unsigned intSizeForNBits(unsigned n) {
    // Disabled until we get better inferred literal types
    //if (n <= 1) return LLVMTypeFor("i1");
    //if (n <= 8) return LLVMTypeFor("i8");
    //if (n <= 16) return LLVMTypeFor("i16");
    if (n <= 32) return 32;
    if (n <= 64) return 64;
    return NULL;
  }

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "IntAST(" << getOriginalText() << ")";
  }
};

IntAST* literalIntAST(int lit);

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val, foster::SourceRange sourceRange)
    : ExprAST(sourceRange), boolValue(val == "true") {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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

  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "CallAST(base = " << str(this->parts[0]) << ", args = ";
    for (size_t i = 1; i < this->parts.size(); ++i) {
      out << " " << str(this->parts[i]) << ", ";
    }
    return out << ")";
  }
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
    : ExprAST(sourceRange), name(name) { this->type = namedType; }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "type " << name << " = " << str(type) << "\n";
  }
};

struct SeqAST : public ExprAST {
  explicit SeqAST(Exprs exprs, foster::SourceRange sourceRange)
    : ExprAST(sourceRange) { this->parts = exprs; }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "TupleExpr(" << str(this->parts[0]) << ")";
  }
};

struct ArrayExprAST : public UnaryExprAST {
  explicit ArrayExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "ArrayExpr(" << str(this->parts[0]) << ")";
  }
};

struct SimdVectorAST : public UnaryExprAST {
  // Implicitly, a SeqAST
  explicit SimdVectorAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "SimdVector(" << str(this->parts[0]) << ")";
  }
};

// base[index]
struct SubscriptAST : public BinaryExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index,
                        foster::SourceRange sourceRange)
    : BinaryExprAST(base, index, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "SubscriptAST(base = " << str(this->parts[0]) << ", index = " << str(this->parts[1]) << ")";
  }
};

// The ->value for a PrototypeAST node is a llvm::Function*
struct PrototypeAST : public ExprAST {
  string name;
  std::vector<VariableAST*> inArgs;
  TypeAST* resultTy;

  foster::SymbolTable<foster::SymbolInfo>::LexicalScope* scope;

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
      this->resultTy = TypeAST::i(32);
    } else {
      //std::cout << "\n\tProtoAST " << name << " ascribed result type of " << *(retTy) << std::endl;
    }
  }

  PrototypeAST(TypeAST* retTy, const string& name,
               const std::vector<VariableAST*>& inArgs,
               foster::SymbolTable<foster::SymbolInfo>::LexicalScope* ascope,
               foster::SourceRange sourceRange)
      : ExprAST(sourceRange),
        name(name), inArgs(inArgs), resultTy(retTy), scope(ascope) {
    ASSERT(scope != NULL);

    if (resultTy == NULL) {
      this->resultTy = TypeAST::i(32);
    } else {
      std::cout << "\n\tProtoAST " << name << " ascribed result type expr of " << str(retTy) << std::endl;
    }
  }

  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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

  std::vector<foster::CFG*> cfgs;

  explicit FnAST(PrototypeAST* proto, ExprAST* body,
                 foster::SourceRange sourceRange)
    : ExprAST(sourceRange),
      proto(proto), body(body),
      wasNested(false), lambdaLiftOnly(false) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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

  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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
      : NamespaceAST(name, parentScope, sourceRange) {
    this->parts = _parts;
  }

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(Module " << scope->getName() << ")";
  }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
};

struct IfExprAST : public ExprAST {
  ExprAST* testExpr, *thenExpr, *elseExpr;
  IfExprAST(ExprAST* testExpr, ExprAST* thenExpr, ExprAST* elseExpr,
            foster::SourceRange sourceRange)
    : ExprAST(sourceRange),
      testExpr(testExpr), thenExpr(thenExpr), elseExpr(elseExpr) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "DerefExprAST(" << str(this->parts[0]) << ")";
  }
};

struct AssignExprAST : public BinaryExprAST {
  explicit AssignExprAST(ExprAST* lhs, ExprAST* rhs, foster::SourceRange sourceRange)
     : BinaryExprAST(lhs, rhs, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) {
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
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(__COMPILES__ " << str(this->parts[0]) << ")";
  }
};


#endif // header guard

