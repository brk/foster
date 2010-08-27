// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "llvm/DerivedTypes.h"
#include "llvm/Constants.h"

#include "base/Assert.h"
#include "base/FilteringIterator.h"
#include "parse/ExprASTVisitor.h"
#include "parse/FosterTypeAST.h"
#include "parse/FosterSymbolTable.h"

#include <vector>
#include <string>

using std::string;
using std::endl;

using llvm::Type;
using llvm::Value;
using llvm::APInt;

class ExprAST; // fwd decl
class TypeAST; // fwd decl

typedef std::vector<ExprAST*> Exprs;
std::ostream& operator<<(std::ostream& out, ExprAST& expr);

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
  virtual std::ostream& operator<<(std::ostream& out) const = 0;
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
  virtual void accept(ExprASTVisitor* visitor) {
    std::cerr << "Visitor called on NamespaceAST! This is probably not desired..." << std::endl;
  }

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
                  foster::SourceRange sourceRange)
        : ExprAST("IntAST", sourceRange), text(originalText), base(base) {
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

IntAST* literalIntAST(int lit, const foster::SourceRange& sourceRange);

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val, foster::SourceRange sourceRange)
    : ExprAST("BoolAST", sourceRange), boolValue(val == "true") {}
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
      : ExprAST("VariableAST", sourceRange),
        name(name), lazilyInsertedPrototype(NULL) {
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
     : UnaryExprAST("UnaryOp", body, sourceRange), op(op) {}
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
     : BinaryExprAST("BinaryOp", lhs, rhs, sourceRange), op(op) {}
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
      : ExprAST("CallAST", sourceRange) {
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
    : ExprAST("NamedTypeDeclAST", sourceRange),
      name(boundName) { this->type = namedType; }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "type " << name << " = " << str(type) << "\n";
  }
};

struct SeqAST : public ExprAST {
  explicit SeqAST(Exprs exprs, foster::SourceRange sourceRange)
    : ExprAST("SeqAST", sourceRange) { this->parts = exprs; }
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

  explicit TupleExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST("TupleExprAST", expr, sourceRange) {
  }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "TupleExpr(" << str(this->parts[0]) << ")";
  }
};

#if 0
struct ArrayExprAST : public UnaryExprAST {
  explicit ArrayExprAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST(expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "ArrayExpr(" << str(this->parts[0]) << ")";
  }
};
#endif

struct SimdVectorAST : public UnaryExprAST {
  // Implicitly, a SeqAST
  explicit SimdVectorAST(ExprAST* expr, foster::SourceRange sourceRange)
    : UnaryExprAST("SimdVectorAST", expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "SimdVector(" << str(this->parts[0]) << ")";
  }
};

// base[index]
struct SubscriptAST : public BinaryExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index,
                        foster::SourceRange sourceRange)
    : BinaryExprAST("SubscriptAST", base, index, sourceRange) {}
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
               const std::vector<VariableAST*>& inArgs,
               foster::SourceRange sourceRange,
               foster::SymbolTable<foster::SymbolInfo>::LexicalScope* ascope = NULL)
      : ExprAST("PrototypeAST", sourceRange),
        name(name), inArgs(inArgs), resultTy(retTy), scope(ascope) {
    if (resultTy == NULL) {
      this->resultTy = TypeAST::i(32);
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
  std::vector<foster::CFG*> cfgs;

  explicit FnAST(PrototypeAST* proto, ExprAST* body,
                 foster::SourceRange sourceRange)
    : ExprAST("FnAST", sourceRange) {
    parts.push_back(proto);
    parts.push_back(body);
  }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "FnAST(proto = " << str(parts[0]) << ", body = " << str(parts[1]) << endl;
  }

  PrototypeAST* getProto() { return dynamic_cast<PrototypeAST*>(parts[0]); }
  ExprAST*& getBody() { return parts[1]; }
};

// A closure stores a typed function pointer and a typed environment pointer.
// At the typechecking level, its type is a function type, but at the codegen level,
// its "external" LLVM type is a struct of function-taking-generic-env-ptr and
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
    : ExprAST("ClosureAST", sourceRange), fn(fn),
      hasKnownEnvironment(false), isTrampolineVersion(false) { }

  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (hasKnownEnvironment && fn) {
      out << "(closure " << str(fn->getProto());
      for (size_t i = 0; i < parts.size(); ++i) {
        out << "\t" << str(parts[i]);
      }
      return out << ")";
    } else if (fn) {
      return out << "(unrefined closure " << str(fn->getProto()) << ")";
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
      : NamespaceAST("ModuleAST", name, parentScope, sourceRange) {
    this->parts = _parts;
  }

  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(Module " << scope->getName() << ")";
  }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
};

struct IfExprAST : public ExprAST {
  IfExprAST(ExprAST* testExpr, ExprAST* thenExpr, ExprAST* elseExpr,
            foster::SourceRange sourceRange)
    : ExprAST("IfExprAST", sourceRange) {
    parts.push_back(testExpr); 
    parts.push_back(thenExpr); 
    parts.push_back(elseExpr); 
  }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "if (" << str(parts[0]) << ")" <<
        " then " << str(parts[1]) << " else " << str(parts[2]);
  }

  ExprAST*& getTestExpr() { ASSERT(parts.size() == 3); return parts[0]; }
  ExprAST*& getThenExpr() { ASSERT(parts.size() == 3); return parts[1]; }
  ExprAST*& getElseExpr() { ASSERT(parts.size() == 3); return parts[2]; }
};

// for var in start to end { body }
struct ForRangeExprAST : public ExprAST {
  VariableAST* var;
  bool _hadExplicitIncrExpr;

  explicit ForRangeExprAST(VariableAST* var,
		  ExprAST* start, ExprAST* end,
                  ExprAST* body, ExprAST* incr,
                  foster::SourceRange sourceRange)
    : ExprAST("ForRangeExprAST", sourceRange), var(var) {
    ASSERT(var);
    _hadExplicitIncrExpr = (incr != NULL);
    if (!_hadExplicitIncrExpr) {
      incr = literalIntAST(1, var->sourceRange);
    }

    ASSERT(start); parts.push_back(start);
    ASSERT(incr ); parts.push_back(incr);
    ASSERT(end  ); parts.push_back(end);
    ASSERT(body ); parts.push_back(body);
  }
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "for " << var->name << " in " << str(parts[0]) << " to " << str(parts[2]);
    if (_hadExplicitIncrExpr) out  << " by " << str(parts[1]);
    out << " do " << str(parts[3]);
    return out;
  }
  
  bool hadExplicitIncrExpr() { return _hadExplicitIncrExpr; }
  ExprAST*& getStartExpr() { ASSERT(parts.size() == 4); return parts[0]; }
  ExprAST*& getIncrExpr()  { ASSERT(parts.size() == 4); return parts[1]; }
  ExprAST*& getEndExpr()   { ASSERT(parts.size() == 4); return parts[2]; }
  ExprAST*& getBodyExpr()  { ASSERT(parts.size() == 4); return parts[3]; }
};

// This class exists only as a placeholder for the env ptr in a closure struct,
// for LLVM to generate a null pointer. 
// For all intents and purposes, it does not exist before the closure
// conversion pass runs
struct NilExprAST : public ExprAST {
  explicit NilExprAST(foster::SourceRange sourceRange)
     : ExprAST("NilExprAST", sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "NilExprAST()";
  }
};


struct RefExprAST : public UnaryExprAST {
  bool isIndirect_;
  explicit RefExprAST(ExprAST* expr, bool isIndirect,
                      foster::SourceRange sourceRange)
    : UnaryExprAST("RefExprAST", expr, sourceRange),
      isIndirect_(isIndirect) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "RefExprAST(" << str(this->parts[0]) << ")";
  }
  
  

  // Returns true if the physical representation of this reference
  // is T** instead of a simple T*.
  virtual bool isIndirect(); // TODO remove, along with inAssignLHS?
};

struct DerefExprAST : public UnaryExprAST {
  explicit DerefExprAST(ExprAST* expr, foster::SourceRange sourceRange)
     : UnaryExprAST("DerefExprAST", expr, sourceRange) {}
  virtual void accept(ExprASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "DerefExprAST(" << str(this->parts[0]) << ")";
  }
};

struct AssignExprAST : public BinaryExprAST {
  explicit AssignExprAST(ExprAST* lhs, ExprAST* rhs, foster::SourceRange sourceRange)
     : BinaryExprAST("AssignExprAST", lhs, rhs, sourceRange) {}
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
     : UnaryExprAST("CompilesExprAST", expr, sourceRange), status(kNotChecked) {}
  // Must manually visit children (for typechecking) because we don't want to codegen our children!
  virtual void accept(ExprASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(__COMPILES__ " << str(this->parts[0]) << ")";
  }
};


#endif // header guard

