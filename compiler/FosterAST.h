// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b2d1e42da6428_98043102
#define H_4b2d1e42da6428_98043102

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

const Type* LLVMTypeFor(const string& name);
void initModuleTypeNames();

///////////////////////////////////////////////////////////

struct ExprAST {
  ExprAST* parent;
  std::vector<ExprAST*> parts;
  
  llvm::Value* value;
  const llvm::Type* type;
  
  explicit ExprAST(ExprAST* parent = NULL) : parent(parent), value(NULL), type(NULL) {}
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) const = 0;
  virtual void accept(FosterASTVisitor* visitor) = 0;
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
class FosterSymbolTable {
  struct LexicalScope {
    string Name;
    typedef std::map<string, T*> Map;
    Map val_of;
    LexicalScope(string name) : Name(name) {}
  };
  typedef std::vector<LexicalScope> Environment;
  Environment env;
 public:
  T* lookup(string ident, string wantedName) {
    for (typename Environment::reverse_iterator it = env.rbegin();
                                                it != env.rend(); ++it) {
      string scopeName = (*it).Name;
      if (scopeName == "*" || wantedName == "" || scopeName == wantedName) {
        T* V = (*it).val_of[ident];
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
  }
  void pushScope(string scopeName) { env.push_back(LexicalScope(scopeName)); }
  void popScope() { env.pop_back(); }
};

extern FosterSymbolTable<Value> scope;
extern FosterSymbolTable<const Type> typeScope;
extern FosterSymbolTable<ExprAST> varScope;
// }}}

struct IntAST : public ExprAST {
  string Text;
  string Clean;
  int Base;
  explicit IntAST(string val, int base = 10): Text(val), Clean(val), Base(base) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  llvm::Constant* getConstantValue();
  
  virtual std::ostream& operator<<(std::ostream& out) const { return out << Clean; }
};

struct BoolAST : public ExprAST {
  bool boolValue;
  explicit BoolAST(string val) : boolValue(val == "true") {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << string(boolValue ? "true" : "false");
  }
};

struct VariableAST : public ExprAST {
  string Name;
  ExprAST* tyExpr;
  // TODO need to figure out how/where/when to assign type info to nil
  explicit VariableAST(const string& name, const llvm::Type* aType): Name(name), tyExpr(NULL) {
    this->type = aType;
    //std::cout << this << " = new VariableAST("<<name<< ", type ptr " << this->type << ")" << std::endl;
  }
  explicit VariableAST(const string& name, ExprAST* tyExpr): Name(name), tyExpr(tyExpr) {
    if (!tyExpr) {
      std::cerr << "Error: " << this << " = VariableAST("<<name<<", type expr NULL)!" << std::endl;
    }
  }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    //if (type) {
    //  return out << Name << " : " << *type;
    //} else {
      return out << Name;
   // }
  }
};

#if 0
  struct StringAST : public ExprAST {
    string Val;
    explicit StringAST(string val): Val(val) {}
    virtual std::ostream& operator<<(std::ostream& out) const { return out << Val; }
    virtual string GetTypeName() { return "String"; }
    virtual bool Sema() { return true; }
    virtual Value* Codegen() {
      //ArrayType* AType = ArrayType::get(Type::Int32Ty, Val.size() + 1);
      //return ConstantArray::get(AType, Val.c_str(), Val.size() + 1);
      //return ConstantArray::get(Val);
      Value* V = Builder.CreateGlobalStringPtr(Val.c_str(), "String_ptr");
      return V;
    }
  };
  
  struct VarDeclAST : public ExprAST {
    string Name;
    string Type;
    ExprAST* Init;
    virtual bool Sema() {
      return true;
    } // TODO
    explicit VarDeclAST(string name, string type, ExprAST* init)
      : Name(name), Type(type), Init(init) {}
    // TODO: associate name with type in symbol table
    virtual string GetTypeName() { return Type; }
    virtual std::ostream& operator<<(std::ostream& out) const {
      out << "\tvar " << Name << " : " << Type;
      if (Init) out << " = " << *Init;
      return out << " ;" << endl;
    }
  #if LLVM
    virtual Value* Codegen() {
      Value* V = Init->Codegen();
      //NamedValues[Name] = V;
    }
  #endif // LLVM
  };
  
  struct UnaryOpAST : public ExprAST {
    string Op;
    ExprAST* AST;
    explicit UnaryOpAST(string op, ExprAST* ast) : Op(op), AST(ast) {}
    virtual string GetTypeName() { return AST->GetTypeName(); }
    virtual bool Sema() {
      if (Op == "!") { return GetTypeName() == "Boolean"; }
      if (Op == "-") { return GetTypeName() == "Int"; }
      return false;
    }
    virtual std::ostream& operator<<(std::ostream& out) const {
      out << Op << "(";
      if (AST) out << *AST; else out << "<nil>";
      return out << ")";
    }
  #if LLVM
    virtual Value* Codegen() {
      Value* V = AST->Codegen();
      if (Op == "!") {
        return Builder.CreateNot(V, "nottmp");
      }
  
      if (Op == "-") {
        return Builder.CreateNeg(V, "negtmp");
      }
  
      fprintf(stderr, "Unknown unary operator '%s'!\n", Op.c_str());
      return NULL;
    }
  #endif // LLVM
  };
  
  struct WhileAST : public ExprAST {
    ExprAST* Cond, *Body;
    WhileAST(ExprAST* cond, ExprAST* body) : Cond(cond), Body(body) {}
    virtual string GetTypeName() { return "Unit"; }
    virtual bool Sema() { return true; } // TODO
    virtual std::ostream& operator<<(std::ostream& out) const {
      out << "while (";
      if (Cond) out << *Cond; else out << "<nil>";
      out << ") { ";
      if (Body) out << *Body; else out << "<nil>";
      return out << " }";
    }
  #if LLVM
    virtual Value* Codegen() {
      return ErrorV("WhileAST.Codegen() not implemented");
    }
  #endif // LLVM
};
#endif

struct BinaryOpExprAST : public BinaryExprAST {
  string op;
  enum { kLHS, kRHS };
  explicit BinaryOpExprAST(string op, ExprAST* lhs, ExprAST* rhs) : BinaryExprAST(lhs, rhs), op(op) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    ExprAST* LHS = this->parts[kLHS];
    ExprAST* RHS = this->parts[kRHS];
    if (LHS) out << *LHS; else out << "<nil>";
    out << ' ' << op << ' ';
    if (RHS) out << *RHS; else out << "<nil>";
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
    return out << "CallAST TODO" << std::endl;
    //out << "(";
    //if (base) out << *this->parts[0]; else out << "<nil>";
    //return out << " " << join(" ", args) << ")";
  }
};

struct SeqAST : public ExprAST {
  explicit SeqAST(Exprs exprs) { this->parts = exprs; }
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "{ ";
    for (int i = 0; i < this->parts.size(); ++i) {
      if (this->parts[i]) {
        if (i > 0) out << " ;\n";
        out << *this->parts[i];
      }
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
    if (!this->parts[0]) {
      return out << "(tuple)";
    }
    return out << "(tuple " << *(this->parts[0]) << ")";
  }
};

struct ArrayExprAST : public UnaryExprAST {
  explicit ArrayExprAST(ExprAST* expr) : UnaryExprAST(expr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    if (!this->parts[0]) {
      return out << "(array)";
    }
    return out << "(array " << *(this->parts[0]) << ")";
  }
};

// base[index]
struct SubscriptAST : public BinaryExprAST {
  explicit SubscriptAST(ExprAST* base, ExprAST* index) : BinaryExprAST(base, index) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << *(this->parts[0]) << "[" << *(this->parts[1]) << "]";
  }
};

struct PrototypeAST : public ExprAST {
  string Name;
  std::vector<VariableAST*> inArgs;
  std::vector<VariableAST*> outArgs;
  
  PrototypeAST(const string& name) : Name(name) {}
  PrototypeAST(const string& name, VariableAST* arg1)
    : Name(name) { inArgs.push_back(arg1); }
  PrototypeAST(const string& name, VariableAST* arg1, VariableAST* arg2)
    : Name(name) { inArgs.push_back(arg1); inArgs.push_back(arg2); }
  PrototypeAST(const string& name, const std::vector<VariableAST*>& inArgs)
    : Name(name), inArgs(inArgs) { }
  PrototypeAST(const string& name, const std::vector<VariableAST*>& inArgs,
                                   const std::vector<VariableAST*>& outArgs)
    : Name(name), inArgs(inArgs), outArgs(outArgs) { }
    
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "fn" << " " << Name << "(";
    for (int i = 0; i < inArgs.size(); ++i) {
      out << inArgs[i]->Name << " ";
    }
    if (!outArgs.empty()) {
      out << " to";
      for (int i = 0; i < outArgs.size(); ++i) {
        out << " " << outArgs[i]->Name;
      }
    }
    out << ")";
    return out;
  }
};

struct FnAST : public ExprAST {
  PrototypeAST* Proto;
  ExprAST* Body;

  explicit FnAST(PrototypeAST* proto, ExprAST* body) : Proto(proto), Body(body) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << (*Proto) << " " << (*Body) << endl;
  }
};

struct IfExprAST : public ExprAST {
  ExprAST* ifExpr, *thenExpr, *elseExpr;
  IfExprAST(ExprAST* ifExpr, ExprAST* thenExpr, ExprAST* elseExpr)
    : ifExpr(ifExpr), thenExpr(thenExpr), elseExpr(elseExpr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    out << "if (";
    if (ifExpr) out << *ifExpr; else out << "<nil>";
    out << ") ";
    if (thenExpr) out << *thenExpr; else out << "<nil>";
    out << " else ";
    if (elseExpr) out << *elseExpr; else out << "<nil>";
    return out;
  }
};

struct UnpackExprAST : public UnaryExprAST {
  explicit UnpackExprAST(ExprAST* expr) : UnaryExprAST(expr) {}
  virtual void accept(FosterASTVisitor* visitor) { visitor->visitChildren(this); visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(unpack " << *(this->parts[0]) << ")";
  }
};

struct BuiltinCompilesExprAST : public UnaryExprAST {
  enum Status { kWouldCompile, kWouldNotCompile, kNotChecked } status;
  explicit BuiltinCompilesExprAST(ExprAST* expr) : UnaryExprAST(expr), status(kNotChecked) {}
  // Must manually visit children (for typechecking) because we don't want to codegen our children!
  virtual void accept(FosterASTVisitor* visitor) { visitor->visit(this); }
  virtual std::ostream& operator<<(std::ostream& out) const {
    return out << "(__COMPILES__ " << *(this->parts[0]) << ")";
  }
};


#endif // header guard

