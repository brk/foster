// vim: set foldmethod=marker :
// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b2d1e42da6428_98043102
#define H_4b2d1e42da6428_98043102

#include "llvm/DerivedTypes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/Constants.h"
#include "llvm/Support/IRBuilder.h"

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

Value* ErrorV(const char* Str);

string join(string glue, Exprs args);

const Type* LLVMTypeFor(const string& name);
void initModuleTypeNames();

///////////////////////////////////////////////////////////

struct ExprAST {
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) = 0;
  virtual const llvm::Type* GetType() = 0;
  virtual bool Sema() = 0;
  virtual Value* Codegen() = 0;
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
  explicit IntAST(string val): Text(val), Clean(val), Base(10) {}
  explicit IntAST(string val, int base): Text(val), Clean(val), Base(base) {}
  virtual const llvm::Type* GetType();
  virtual std::ostream& operator<<(std::ostream& out) { return out << Clean; }
  virtual bool Sema() { std::cout << "IntAST::Sema() -> true" << std::endl; return true; }
  virtual Value* Codegen();
};

struct VariableAST : public ExprAST {
  string Name;
  // TODO need to figure out how/where/when to assign type info to nil
  const llvm::Type* type;
  virtual const llvm::Type* GetType() {
    std::cout << "Returning " << type << " for variable\t" << Name << std::endl;
    return type;
  }
  explicit VariableAST(const string& name, const llvm::Type* type): Name(name), type(type) {
    std::cout << "new VariableAST("<<name<< ", " << type << ")" << std::endl;
  }
  virtual std::ostream& operator<<(std::ostream& out) {
    //if (type) {
    //  return out << Name << " : " << *type;
    //} else {
      return out << Name;
   // }
  }
  virtual bool Sema() {
    if (Name == "nil") return true;
    // TODO
    std::cout << "VariableAST::Sema() -> true" << std::endl;
    return true;
  }
  virtual Value* Codegen() {
    std::cout << "\t" << "Codegen variable "  << Name << std::endl;
    Value* V = scope.lookup(Name, "");
    return V ? V : ErrorV(("Unknown variable name " + Name).c_str());
  }
};

#if 0
  struct StringAST : public ExprAST {
    string Val;
    explicit StringAST(string val): Val(val) {}
    virtual std::ostream& operator<<(std::ostream& out) { return out << Val; }
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
    virtual std::ostream& operator<<(std::ostream& out) {
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
    virtual std::ostream& operator<<(std::ostream& out) {
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
    virtual std::ostream& operator<<(std::ostream& out) {
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

struct BinaryExprAST : public ExprAST {
  string op;
  ExprAST* LHS, *RHS;
  BinaryExprAST(string op, ExprAST* lhs, ExprAST* rhs)
    : op(op), LHS(lhs), RHS(rhs) {}
  virtual bool Sema();
  virtual const llvm::Type* GetType();
  virtual std::ostream& operator<<(std::ostream& out) {
    if (LHS) out << *LHS; else out << "<nil>";
    out << ' ' << op << ' ';
    if (RHS) out << *RHS; else out << "<nil>";
  }
  virtual Value* Codegen();
};


#if 0
  struct DispatchAST : public ExprAST {
    string Label;
    ExprAST* Expr; // Expr . label (args)
    Exprs Args;
    DispatchAST(ExprAST* expr, string label, Exprs args) : Label(label), Expr(expr), Args(args) {}
    virtual bool Sema() { return true; } // TODO
    virtual string GetTypeName() { return "<not implemented>"; }
    virtual std::ostream& operator<<(std::ostream& out) {
      if (Expr) out << *Expr; else out << "<nil>";
      return out << "." << Label << "(" << join(", ", Args) << ")";
    }
    virtual Value* Codegen() {
      Value* Obj = Expr->Codegen();
      const Type* ObjTy = Obj->getType();
      string ClassType = Expr->GetTypeName();
      if (true) { // TODO differentiate static vs virtual methods
        Value* Method = staticMethods[std::make_pair(ClassType, Label)];
        assert(Method);
        std::stringstream ss; ss << "called_" << ClassType << "." << Label;
        return Builder.CreateCall(Method, Obj, ss.str().c_str());
      }
      return ErrorV("DispatchAST.Codegen() not implemented");
    }
  };
  
  struct NewExprAST : public ExprAST {
    string Type;
    Exprs Actuals;
    virtual bool Sema() {
      // TODO: "The class must have the same number of formals as expressions as given here
      // and the types must match (as in a  dispatch).
      return true;
    }
    NewExprAST(string type, Exprs actuals) : Type(type), Actuals(actuals) {}
    virtual string GetTypeName() { return Type; }
    virtual std::ostream& operator<<(std::ostream& out) {
      return out << "new " << Type << "(" << Actuals << ")";
    }
    virtual Value* Codegen() {
      std::stringstream ss; ss << "new_" << Type;
      const llvm::Type* Ty = LLVMType_from(Type);
      assert(Ty);
      return Builder.CreateMalloc(Ty, (Value*)0, ss.str().c_str());
    }
  };
#endif

// base(args)
struct CallAST : public ExprAST {
  ExprAST* base;
  Exprs args;
  CallAST(ExprAST* base, Exprs args) : base(base), args(args) {}
  virtual bool Sema() {
    const Type* baseType = base->GetType();
    if (baseType == NULL) {
      std::cerr << "Error: CallAST base expr returned null type" << std::endl;
      return false;
    }
    
    const llvm::FunctionType* baseFT = llvm::dyn_cast<const llvm::FunctionType>(baseType);
    if (baseFT == NULL) {
      std::cerr << "Error: CallAST base expr had non-function type " << *baseType << std::endl;
      return false;
    }
    
    int numParams = baseFT->getNumParams();
    if (numParams != args.size()) {
      std::cerr << "Error: arity mismatch; " << args.size() << " args provided"
        << " for function taking " << numParams << " args." << std::endl;
      return false;
    }
    
    bool success = true;
    for (int i = 0; i < numParams; ++i) {
      const Type* formalType = baseFT->getParamType(i);
      const Type* actualType = args[i]->GetType();
      if (formalType != actualType) {
        success = false;
        std::cerr << "Type mismatch between actual and formal arg " << i << std::endl;
        std::cerr << "\tformal: " << *formalType << "; actual: " << *actualType << std::endl;
      }
    }
    
    return success;
  }
  
  virtual const llvm::Type* GetType() {
    if (this->Sema()) {
      return llvm::dyn_cast<const llvm::FunctionType>(base->GetType())->getReturnType();
    } else {
      return NULL;
    }
  }
  
  virtual std::ostream& operator<<(std::ostream& out) {
    out << "(";
    if (base) out << *base; else out << "<nil>";
    return out << " " << join(" ", args) << ")";
  }
  virtual Value* Codegen() {
    std::cout << "\t" << "Codegen callast "  << *base << std::endl;
    
    Value* FV = base->Codegen();
    Function* F = llvm::dyn_cast_or_null<Function>(FV);
    if (!F) {
      std::cerr << "base: " << *base << "; FV: " << FV << std::endl;
      return ErrorV("Unknown function referenced");
    }
    
    if (F->arg_size() != args.size()) {
      std::stringstream ss;
      ss << "Function " << (*base) <<  " got " << args.size() << " args, expected "<< F->arg_size();
      return ErrorV(ss.str().c_str());
    }
    
    std::vector<Value*> valArgs;
    for (int i = 0; i < args.size(); ++i) {
      Value* V = args[i]->Codegen();
      if (!V) return NULL;
      valArgs.push_back(V);
    }
    
    return builder.CreateCall(F, valArgs.begin(), valArgs.end(), "calltmp");
  }
};

struct SeqAST : public ExprAST {
  Exprs exprs;
  virtual bool Sema() {
    bool success = true;
    for (int i = 0; i < exprs.size(); ++i) {
      if (exprs[i]) {
        success = exprs[i]->Sema() && success;
      } else {
        std::cerr << "Null expr in SeqAST" << std::endl;
        return false;
      }
    }
    return success;
  }
  explicit SeqAST(Exprs exprs) : exprs(exprs) {}
  virtual const llvm::Type* GetType() {
    if (exprs.empty()) { return NULL; }
    else { return exprs[exprs.size() - 1]->GetType(); }
  }
  
  virtual std::ostream& operator<<(std::ostream& out) {
    out << "{ ";
    for (int i = 0; i < exprs.size(); ++i) {
      if (exprs[i]) {
        if (i > 0) out << " ;\n";
        out << *exprs[i];
      }
    }
    return out << " }";
  }
  
  virtual Value* Codegen() {
    Value* V;
    for (int i = 0; i < exprs.size(); ++i) {
      if (exprs[i]) V = exprs[i]->Codegen();
      else {
        std::cerr << "SeqAST::Codegen() saw null seq expression " << i << std::endl;
        break;
      }
    }
    return V;
  }
};

struct TupleExprAST : public ExprAST {
  SeqAST* body;
  Value* cachedValue;
  virtual bool Sema() { std::cout << "TupleExprAST::Sema() -> true" << std::endl; return true; } // TODO
  explicit TupleExprAST(ExprAST* expr) : cachedValue(NULL) {
    body = dynamic_cast<SeqAST*>(expr);
  }
  virtual const llvm::Type* GetType();
  virtual std::ostream& operator<<(std::ostream& out) {
    return out << "(tuple " << *body << ")";
  }
  
  virtual Value* Codegen();
};

struct SubscriptAST : public ExprAST {
  ExprAST* base;
  ExprAST* index;
  virtual bool Sema() { std::cout << "SubscriptAST::Sema() -> true" << std::endl; return true; } // TODO
  explicit SubscriptAST(ExprAST* base, ExprAST* index)
    : base(base), index(index) { }
  virtual const llvm::Type* GetType() {
    std::cout << "SubscriptAST::GetType() -> NULL..." << std::endl;
    return NULL;
  }
  virtual std::ostream& operator<<(std::ostream& out) {
    return out << *base << "[" << *index << "]";
  }
  
  virtual Value* Codegen();
};

struct PrototypeAST : public ExprAST {
  string Name;
  std::vector<VariableAST*> inArgs;
  std::vector<VariableAST*> outArgs;
  virtual bool Sema();
  const llvm::FunctionType* GetType();
  
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
    
  llvm::Function* Codegen();
  virtual std::ostream& operator<<(std::ostream& out) {
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

  virtual bool Sema() {
    bool p = Proto->Sema(); bool b = Body->Sema();
    return p && b; // Check both parts even if there's an error in one...(?)
  }
  virtual const llvm::Type* GetType() {
    std::cout << "FnAST::GetType() -> NULL..." << std::endl;
    return NULL;
  }
  explicit FnAST(PrototypeAST* proto, ExprAST* body) :
      Proto(proto), Body(body) {
    }

  virtual std::ostream& operator<<(std::ostream& out) {
    return out << (*Proto) << " " << (*Body) << endl;
  }
  llvm::Function* Codegen();
};

struct IfExprAST : public ExprAST {
  ExprAST* ifExpr, *thenExpr, *elseExpr;
  IfExprAST(ExprAST* ifExpr, ExprAST* thenExpr, ExprAST* elseExpr)
    : ifExpr(ifExpr), thenExpr(thenExpr), elseExpr(elseExpr) {}
  public:
  virtual bool Sema() { std::cout << "IfExprAST::Sema() -> true" << std::endl;  return true; } // TODO
  virtual const llvm::Type* GetType() {
    std::cout << "IfExprAST::GetType() -> NULL..." << std::endl;
    // Return unification of thenExpr and elseExpr types
    return NULL;
  }
  
  virtual std::ostream& operator<<(std::ostream& out) {
    out << "if (";
    if (ifExpr) out << *ifExpr; else out << "<nil>";
    out << ") ";
    if (thenExpr) out << *thenExpr; else out << "<nil>";
    out << " else ";
    if (elseExpr) out << *elseExpr; else out << "<nil>";
    return out;
  }
  virtual Value* Codegen();
};

#endif // header guard
