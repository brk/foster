// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_AST_H
#define FOSTER_AST_H

#include "llvm/DerivedTypes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Constants.h"
#include "llvm/Support/IRBuilder.h"

#include "FosterASTVisitor.h"

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

class ExprAST; // fwd decl

typedef std::vector<ExprAST*> Exprs;
std::ostream& operator<<(std::ostream& out, ExprAST& expr);

void fosterLLVMInitializeNativeTarget();

string freshName(string like);

extern llvm::ExecutionEngine* ee;
extern llvm::IRBuilder<> builder;
extern Module* module;

string join(string glue, Exprs args);
string str(ExprAST* expr);

const Type* LLVMTypeFor(const string& name);
void initModuleTypeNames();

inline bool isSmallPowerOfTwo(int x) {
  return (x == 2) || (x == 4) || (x == 8) || (x == 16);
}

///////////////////////////////////////////////////////////

template <typename T>
struct NameResolver {
  virtual T* lookup(const string& name, const string& meta) = 0;
};

struct ExprAST : public NameResolver<ExprAST> {
  ExprAST* parent;
  std::vector<ExprAST*> parts;
  
  llvm::Value* value;
  const llvm::Type* type;
  
  explicit ExprAST(ExprAST* parent = NULL) : parent(parent), value(NULL), type(NULL) {}
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) const = 0;
  virtual void accept(FosterASTVisitor* visitor) = 0;
  virtual ExprAST* lookup(const string& name, const string& meta) {
    std::cerr << "ExprAST.lookup() called!" << std::endl;
    return NULL;
  }
};

struct UnaryExprAST : public ExprAST {
  explicit UnaryExprAST(ExprAST* e1) { this->parts.push_back(e1); }
};

struct BinaryExprAST : public ExprAST {
  explicit BinaryExprAST(ExprAST* e1, ExprAST* e2) {
    this->parts.push_back(e1);
    this->parts.push_back(e2);
  }
};

// {{{ |scope| maps names (var/fn) to llvm::Value*/llvm::Function*
template <typename T>
class FosterSymbolTable : public NameResolver<T> {
  struct LexicalScope {
    string name;
    typedef std::map<string, T*> Map;
    Map val_of;
    T* lookup(const string& ident) {
      T* rv = val_of[ident];
      return rv;
    }
    LexicalScope(string name) : name(name) {}
    void dump(std::ostream& out) {
      out << "\t" << name << std::endl;
      for (typename Map::iterator it = val_of.begin(); it != val_of.end(); ++it) {
        out << "\t\t" << (*it).first << ": " << (*it).second << std::endl;
      }
    }
  };
  typedef std::vector<LexicalScope> Environment;
  Environment env;
 public:
  virtual T* lookup(const string& ident, const string& wantedName) {
    for (typename Environment::reverse_iterator it = env.rbegin();
                                                it != env.rend(); ++it) {
      string scopeName = (*it).name;
      if (scopeName == "*" || wantedName == "" || scopeName == wantedName) {
        T* V = (*it).lookup(ident);
        if (V != NULL) return V;
      }
    }
    return NULL;
  }

  T* insert(string ident, T* V) {
    if (env.empty()) {
      std::cerr << "Inserted into empty symbol table!" << std::endl;
      pushScope("*");
    }
    env.back().val_of[ident] = V;
    return V;
  }
  void pushScope(string scopeName) {
    env.push_back(LexicalScope(scopeName));
  }
  void popScope() {
    env.pop_back();
  }
  void dump(std::ostream& out) {
    for (int i = 0; i < env.size(); ++i) {
      env[i].dump(out);
    }
  }
};

extern FosterSymbolTable<Value> scope;
extern FosterSymbolTable<const Type> typeScope;
extern FosterSymbolTable<ExprAST> varScope;
// }}}

// "Fake" AST node for doing iterative lookup; AST stand-in for namespaces.
struct NameResolverAST : public ExprAST {
  FosterSymbolTable<ExprAST> localScope;
  const std::string& scopeName;

  explicit NameResolverAST(const std::string& name) : scopeName(name) {
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
  explicit IntAST(string originalText, string valText, int base = 10)
    : Text(originalText), Clean(valText), Base(base) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  llvm::Constant* getConstantValue();
  llvm::APInt getAPInt();
  
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << Text;
  }
};

IntAST* literalIntAST(int lit);

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val) : boolValue(val == "true") {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << string(boolValue ? "true" : "false");
  }
};

struct VariableAST : public ExprAST {
  string name;
  ExprAST* tyExpr;
  PrototypeAST* lazilyInsertedPrototype;
  bool noInitialType;
  bool noFixedType() { return noInitialType && !tyExpr && !type; }

  explicit VariableAST(const string& name)
      : name(name), tyExpr(NULL), lazilyInsertedPrototype(NULL) { // of as-yet-undetermined type
    this->type = NULL;
    noInitialType = true;
    std::cout << "new variable named " << name << " of no fixed type..." << std::endl;
  }

  // TODO need to figure out how/where/when to assign type info to nil
  explicit VariableAST(const string& name, const llvm::Type* aType)
      : name(name), tyExpr(NULL), lazilyInsertedPrototype(NULL) {
    this->type = aType;
    noInitialType = false;
  }
  explicit VariableAST(const string& name, ExprAST* tyExpr)
      : name(name), tyExpr(tyExpr), lazilyInsertedPrototype(NULL) {
    noInitialType = false;
    if (!tyExpr) {
      std::cerr << "Error: " << this << " = VariableAST("<<name<<", type expr NULL)!" << std::endl;
    }
  }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (type) {
      return out << name << " : " << *type;
    } else {
      return out << name;
    }
  }
};

struct UnaryOpExprAST : public UnaryExprAST {
  string op;
  explicit UnaryOpExprAST(string op, ExprAST* body) : UnaryExprAST(body), op(op) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << '(' << op << ' ' << str(this->parts[0]) << ")";
  }
};

struct BinaryOpExprAST : public BinaryExprAST {
  string op;
  enum { kLHS, kRHS };
  explicit BinaryOpExprAST(string op, ExprAST* lhs, ExprAST* rhs) : BinaryExprAST(lhs, rhs), op(op) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    ExprAST* LHS = this->parts[kLHS];
    ExprAST* RHS = this->parts[kRHS];
    return out << "(" << str(LHS) << " " << op << " "  << str(RHS) << ")";
  }
};

// base(args)
struct CallAST : public ExprAST {
  CallAST(ExprAST* base, Exprs args) {
    parts.push_back(base);
    for (int i = 0; i < args.size(); ++i) parts.push_back(args[i]);
  }
  // For now, call exprs must manually visit children in case of UnpackExprs
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << str(this->parts[0]) << "(";
    for (int i = 1; i < this->parts.size(); ++i) {
      out << " " << str(this->parts[i]);
    }
    return out << ")";
  }
};

struct SeqAST : public ExprAST {
  explicit SeqAST(Exprs exprs) { this->parts = exprs; }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "{ ";
    for (int i = 0; i < this->parts.size(); ++i) {
      if (i > 0) out << " ;\n";
      out << str(this->parts[i]);
    }
    return out << " }";
  }
};

struct TupleExprAST : public UnaryExprAST {
  explicit TupleExprAST(ExprAST* expr) : UnaryExprAST(expr) {
    std::cout << "\t\t\tTupleExprAST " << expr << " ; " << this->parts[0] << std::endl;
  }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(tuple " << str(this->parts[0]) << ")";
  }
};

struct ArrayExprAST : public UnaryExprAST {
  explicit ArrayExprAST(ExprAST* expr) : UnaryExprAST(expr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(array " << str(this->parts[0]) << ")";
  }
};

struct SimdVectorAST : public UnaryExprAST {
  // Implicitly, a SeqAST
  explicit SimdVectorAST(ExprAST* expr) : UnaryExprAST(expr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(simd-vector " << str(this->parts[0]) << ")";
  }
};

// base[index]
struct SubscriptAST : public BinaryExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index) : BinaryExprAST(base, index) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << str(this->parts[0]) << "[" << str(this->parts[1]) << "]";
  }
};

// The ->value for a PrototypeAST node is a llvm::Function*
struct PrototypeAST : public ExprAST {
  string name;
  std::vector<VariableAST*> inArgs;
  const Type* resultTy;
  ExprAST* tyExpr;

  PrototypeAST(const Type* retTy, const string& name)
    : name(name), resultTy(retTy), tyExpr(NULL) {}

  PrototypeAST(const Type* retTy, const string& name, VariableAST* arg1)
    : name(name), resultTy(retTy), tyExpr(NULL) { inArgs.push_back(arg1); }

  PrototypeAST(const Type* retTy, const string& name, VariableAST* arg1, VariableAST* arg2)
    : name(name), resultTy(retTy), tyExpr(NULL) { inArgs.push_back(arg1); inArgs.push_back(arg2); }

  PrototypeAST(const Type* retTy, const string& name, const std::vector<VariableAST*>& inArgs)
    : name(name), resultTy(retTy), tyExpr(NULL), inArgs(inArgs) { }

  PrototypeAST(const string& name, const std::vector<VariableAST*>& inArgs, const Type* retTy)
    : name(name), resultTy(retTy), tyExpr(NULL), inArgs(inArgs) {
    if (resultTy == NULL) {
      this->resultTy = LLVMTypeFor("i32");
    } else {
      std::cout << "\n\tProtoAST " << name << " ascribed result type of " << *(resultTy) << std::endl;
    }
  }

  PrototypeAST(const string& name, const std::vector<VariableAST*>& inArgs, ExprAST* retTyExpr)
      : name(name), resultTy(NULL), inArgs(inArgs), tyExpr(retTyExpr) {
      if (tyExpr == NULL) {
        this->resultTy = LLVMTypeFor("i32");
      } else {
        std::cout << "\n\tProtoAST " << name << " ascribed result type expr of " << *(tyExpr) << std::endl;
      }
    }
    
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "fn" << " " << name << "(";
    for (int i = 0; i < inArgs.size(); ++i) {
      out << str(inArgs[i]) << " ";
    }
    if (resultTy != NULL) {
      out << " to " << (*resultTy);
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

  explicit FnAST(PrototypeAST* proto, ExprAST* body)
    : proto(proto), body(body), wasNested(false), lambdaLiftOnly(false) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << str(proto) << "\n\t" << str(body) << endl;
  }
};

struct ClosureTypeAST : public ExprAST {
  PrototypeAST* proto;
  
  explicit ClosureTypeAST(FnAST* fn) : proto(fn->proto) {}
  
  virtual void accept(FosterASTVisitor* visitor) {
    visitor->visit(this);
  }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(type closure " << str(proto) << ")";
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

  explicit ClosureAST(FnAST* fn, const Exprs& envExprs)
    : fn(fn), hasKnownEnvironment(true) {
      this->parts = envExprs;
      //fn->parent = this;
  }

  explicit ClosureAST(FnAST* fn) : fn(fn), hasKnownEnvironment(false) {
    //fn->parent = this;
  }
  
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (hasKnownEnvironment && fn) {
      out << "(closure " << str(fn->proto);
      for (int i = 0; i < parts.size(); ++i) {
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
  IfExprAST(ExprAST* testExpr, ExprAST* thenExpr, ExprAST* elseExpr)
    : testExpr(testExpr), thenExpr(thenExpr), elseExpr(elseExpr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "if (" << str(testExpr) << ")" <<
        " then " << str(thenExpr) << " else " << str(elseExpr);
  }
};

struct RefExprAST : public UnaryExprAST {
  explicit RefExprAST(ExprAST* expr) : UnaryExprAST(expr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(ref " << str(this->parts[0]) << ")";
  }
};

struct DerefExprAST : public UnaryExprAST {
  explicit DerefExprAST(ExprAST* expr) : UnaryExprAST(expr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(deref " << str(this->parts[0]) << ")";
  }
};

struct AssignExprAST : public BinaryExprAST {
  explicit AssignExprAST(ExprAST* lhs, ExprAST* rhs) : BinaryExprAST(lhs, rhs) {}
  virtual void accept(FosterASTVisitor* visitor) {
    visitor->inAssignLHS = true;
    parts[0]->accept(visitor);
    visitor->inAssignLHS = false;

    parts[1]->accept(visitor);
    visitor->visit(this);
  }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "set " << str(this->parts[0]) << " = " << str(parts[1]) << std::endl;
  }
};

struct UnpackExprAST : public UnaryExprAST {
  explicit UnpackExprAST(ExprAST* expr) : UnaryExprAST(expr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(unpack " << str(this->parts[0]) << ")";
  }
};

struct BuiltinCompilesExprAST : public UnaryExprAST {
  enum Status { kWouldCompile, kWouldNotCompile, kNotChecked } status;
  explicit BuiltinCompilesExprAST(ExprAST* expr) : UnaryExprAST(expr), status(kNotChecked) {}
  // Must manually visit children (for typechecking) because we don't want to codegen our children!
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(__COMPILES__ " << str(this->parts[0]) << ")";
  }
};


#endif // header guard

