#ifndef H_4b3f24963055d7_81582449
#define H_4b3f24963055d7_81582449

#include "FosterASTVisitor.h"

struct TypecheckPass : public FosterASTVisitor {
  bool typeParsingMode;
  TypecheckPass() : typeParsingMode(false) {}
  
  // Parse an AST as a type specification; the primary difference from the main
  // TypecheckPass is that the "type" of a variable is determined from its name;
  // e.g. VariableAST("i32", ...) yields LLVMTypeFor("i32") instead of inspecting
  // the "provided" type.
  
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


  
