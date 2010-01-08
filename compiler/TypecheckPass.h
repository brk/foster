#ifndef H_4b3f24963055d7_81582449
#define H_4b3f24963055d7_81582449

#include "FosterASTVisitor.h"

struct TypecheckPass : public FosterASTVisitor {
  virtual void visit(FnAST* ast);
  virtual void visit(SeqAST* ast);
  virtual void visit(BoolAST* ast);
  virtual void visit(CallAST* ast);
  virtual void visit(IntAST*  ast);
  virtual void visit(IfExprAST* ast);
  virtual void visit(VariableAST* ast);
  virtual void visit(ArrayExprAST* ast);
  virtual void visit(PrototypeAST* ast);
  virtual void visit(TupleExprAST* ast);
  virtual void visit(SubscriptAST* ast);
  virtual void visit(BinaryExprAST* ast);
  virtual void visit(BuiltinCompilesExprAST* ast);
};

#endif // header guard


  
