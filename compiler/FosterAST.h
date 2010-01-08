

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

using std::string;
using std::endl;

using llvm::Type;
using llvm::Module;
using llvm::Value;
using llvm::getGlobalContext;
using llvm::APInt;

class ExprAST; // fwd decl

typedef std::vector<ExprAST*> Exprs;
std::ostream& operator<<(std::ostream& out, ExprAST& expr);

void fosterLLVMInitializeNativeTarget();

extern llvm::ExecutionEngine* ee;
extern llvm::IRBuilder<> Builder;
extern Module* TheModule;
extern std::map<string, const Type*> NamedTypes;

Value* ErrorV(const char* Str);
const Type* LLVMType_from(string s);

///////////////////////////////////////////////////////////

struct ExprAST {
  virtual ~ExprAST() {}
  virtual std::ostream& operator<<(std::ostream& out) = 0;
  virtual string GetTypeName() = 0;
  virtual bool Sema() = 0;
  virtual Value* Codegen() = 0;
};

// {{{ Foster symbol table Env
class FosterSymbolTable {
  struct LexicalScope {
    string Name;
    typedef std::map<string, ExprAST*> Map;
    Map AST_of;
    LexicalScope(string name) : Name(name) {}
  };
  typedef std::vector<LexicalScope> Environment;
  Environment env;
public:
  const ExprAST* lookup(string ident, string wantedName) {
    for (Environment::reverse_iterator it = env.rbegin(); it != env.rend(); ++it) {
      string scopeName = (*it).Name;
      if (scopeName == "*" || wantedName == "" || scopeName == wantedName) {
        const ExprAST* ast = (*it).AST_of[ident];
        if (ast != NULL) return ast;
      }
    }
    return NULL;
  }

  ExprAST* insert(string ident, ExprAST* ast) { env.back().AST_of[ident] = ast; }
  void pushScope(string scopeName) { env.push_back(LexicalScope(scopeName)); }
  void popScope() { env.pop_back(); }
};

//FosterSymbolTable Env;
// }}}

struct IntAST : public ExprAST {
  string Text;
  string Clean;
  int Base;
  explicit IntAST(string val): Text(val), Clean(val), Base(10) {}
  explicit IntAST(string val, int base): Text(val), Clean(val), Base(base) {}
  virtual string GetTypeName() { return "Int"; }
  virtual std::ostream& operator<<(std::ostream& out) { return out << Clean; }
  virtual bool Sema() { return true; }
  virtual Value* Codegen();
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

struct VariableAST : public ExprAST {
  std::string Name;
  // TODO need to figure out how/where/when to assign type info to null
  virtual string GetTypeName() { return "<not implemented>"; }
  explicit VariableAST(const string& name): Name(name) {}
  virtual std::ostream& operator<<(std::ostream& out) { return out << Name; }
  virtual bool Sema() {
    if (Name == "null") return true;
    // TODO
    return true;
  }
#if LLVM
  virtual Value* Codegen() {
    //Value* V = NamedValues[Name];
    // if Name is null, we need to decide what type it ought to take before doing codegen...
    //return V ? V : ErrorV(("Unknown variable name " + Name).c_str());
    return NULL;
  }
#endif
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

struct IfExprAST : public ExprAST {
  ExprAST* A, *B, *C;
  IfExprAST(ExprAST* a, ExprAST* b, ExprAST* c) : A(a), B(b), C(c) {}
  private:
    string GetCondTypeName() { return A->GetTypeName(); }
    string GetResultTypeName() { return B->GetTypeName(); }
    // TODO return typeJoin(B->GetTypeName(), C->GetTypeName);
  public:
  virtual bool Sema() { return true; } // TODO
  virtual string GetTypeName() {
    string CondTypeName = GetCondTypeName();
    if (CondTypeName != "Boolean") {
      fprintf(stderr, "if expression condition has non-Boolean type %s\n", CondTypeName.c_str());
      return "Unit";
    }
    return GetResultTypeName();
  }
  virtual std::ostream& operator<<(std::ostream& out) {
    out << "if (";
    if (A) out << *A; else out << "<nil>";
    out << ") ";
    if (B) out << *B; else out << "<nil>";
    out << " else ";
    if (C) out << *C; else out << "<nil>";
    return out;
  }
#if LLVM
  virtual Value* Codegen() {
    Value* Cond = A->Codegen();
    if (!Cond) return NULL;

    Cond = Builder.CreateICmpEQ(Cond, ConstantInt::get(APInt(32, 0)), "ifcond");
    Function *TheFunction = Builder.GetInsertBlock()->getParent();

    BasicBlock* ThenBB = BasicBlock::Create("then", TheFunction);
    BasicBlock* ElseBB = BasicBlock::Create("else");
    BasicBlock* MergeBB = BasicBlock::Create("ifcont");

    Builder.CreateCondBr(Cond, ThenBB, ElseBB);
    Builder.SetInsertPoint(ThenBB);

    Value* Then = B->Codegen();
    if (!Then) {
      return ErrorV("Codegen for if condition failed due to missing Value for 'then' part");
    }

    Builder.CreateBr(MergeBB);
    ThenBB = Builder.GetInsertBlock();

    TheFunction->getBasicBlockList().push_back(ElseBB);
    Builder.SetInsertPoint(ElseBB);

    Value* Else = C->Codegen();
    if (!Else) {
      return ErrorV("Codegen for if condition failed due to missing Value for 'else' part");
    }

    Builder.CreateBr(MergeBB);
    ElseBB = Builder.GetInsertBlock();

    TheFunction->getBasicBlockList().push_back(MergeBB);
    Builder.SetInsertPoint(MergeBB);
    const Type* resultType = LLVMType_from(GetResultTypeName());
    PHINode *PN = Builder.CreatePHI(resultType, "iftmp");

    PN->addIncoming(Then, ThenBB);
    PN->addIncoming(Else, ElseBB);
    return PN;
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
  string Op;
  ExprAST* LHS, *RHS;
  BinaryExprAST(string op, ExprAST* lhs, ExprAST* rhs) : Op(op), LHS(lhs), RHS(rhs) {}
  virtual bool Sema() {
    return LHS->GetTypeName() == "Int" &&
           RHS->GetTypeName() == "Int";
  }
  virtual string GetTypeName() {
    // type checking of consitituent parts done in semantic analysis phase

    if (Op == "<" || Op == "<=") {
      return "Boolean";
    }

    if (Op == "+" || Op == "-" || Op =="*" || Op == "/") {
      return "Int";
    }
  }
  virtual std::ostream& operator<<(std::ostream& out) {
    if (LHS) out << *LHS; else out << "<nil>";
    out << ' ' << Op << ' ';
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

struct BlockAST : public ExprAST {
  Exprs Expressions;
  virtual bool Sema() { return true; } // TODO
  explicit BlockAST(Exprs exprs) : Expressions(exprs) {}
  virtual string GetTypeName() {
    if (Expressions.size() == 0) return "Unit";
    if (Expressions.size() == 1) return Expressions[0]->GetTypeName();
    // TODO: is this correct? p19
    return Expressions[Expressions.size()-1]->GetTypeName();
  }
  virtual std::ostream& operator<<(std::ostream& out) {
    out << "{ ";
    for (int i = 0; i < Expressions.size(); ++i) {
      if (Expressions[i]) {
        if (i > 0) out << " ; ";
        out << *Expressions[i];
      }
    }
    return out << " }";
  }
  virtual Value* Codegen() {
    //BB = Builder.GetInsertBlock();
    Value* V;
    for (int i = 0; i < Expressions.size(); ++i) {
      if (Expressions[i]) V = Expressions[i]->Codegen();
      else break;
    }
    return V;
  }
};
#endif


struct PrototypeAST {
  string Name;
  std::vector<string> Args;
  PrototypeAST(const string& name) : Name(name) {}
  PrototypeAST(const string& name, const string& arg1)
    : Name(name) { Args.push_back(arg1); }
  PrototypeAST(const string& name, const string& arg1, const string& arg2)
    : Name(name) { Args.push_back(arg1); Args.push_back(arg2); }
  PrototypeAST(const string& name, const std::vector<string>& args)
    : Name(name), Args(args) {}

  llvm::Function* Codegen();
};

struct FnAST : public ExprAST {
  PrototypeAST* Proto;
  ExprAST* Body;

  virtual bool Sema() { return true; } // TODO
  virtual string GetTypeName() { return "TODO"; }
  explicit FnAST(PrototypeAST* proto, ExprAST* body) :
      Proto(proto), Body(body) {
    }

  virtual std::ostream& operator<<(std::ostream& out) {
    out << "fn TODO" << endl;
  }
  llvm::Function* Codegen();
};

#endif // header guard
