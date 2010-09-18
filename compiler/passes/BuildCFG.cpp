// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "parse/FosterAST.h"

#include "passes/BuildCFG.h"

#include "parse/ExprASTVisitor.h"

struct BuildCFG : public ExprASTVisitor {
  #include "parse/ExprASTVisitor.decls.inc.h"

  virtual void visitChildren(ExprAST* ast) {
    // Only visit children manually!
  }

  foster::CFG* currentRoot;
  FnAST* currentFn;
};

namespace foster {
  void buildCFG(ModuleAST* ast) {
    BuildCFG b; ast->accept(&b);
  }
}


using foster::SourceRange;
using foster::CFG;

void absorb(BuildCFG* pass, Exprs& exprs) {
  for (Exprs::iterator it = exprs.begin(); it != exprs.end(); ++it) {
    ExprAST* ast = (*it);
    ast->accept(pass);
  }
}

void BuildCFG::visit(IntAST* ast)          { currentRoot->append(ast); }
void BuildCFG::visit(BoolAST* ast)         { currentRoot->append(ast); }
void BuildCFG::visit(VariableAST* ast)     { currentRoot->append(ast); }
void BuildCFG::visit(UnaryOpExprAST* ast)  { currentRoot->append(ast); }
void BuildCFG::visit(BinaryOpExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(NilExprAST* ast)      { currentRoot->append(ast); }
void BuildCFG::visit(RefExprAST* ast)      { currentRoot->append(ast); }
void BuildCFG::visit(DerefExprAST* ast)    { currentRoot->append(ast); }
void BuildCFG::visit(AssignExprAST* ast)   { currentRoot->append(ast); }
void BuildCFG::visit(SubscriptAST* ast)    { currentRoot->append(ast); }
void BuildCFG::visit(ClosureAST* ast)      { currentRoot->append(ast); }
///void BuildCFG::visit(ArrayExprAST* ast) { currentRoot->append(ast); }
///void BuildCFG::visit(SimdVectorAST* ast)   { currentRoot->append(ast); } 
void BuildCFG::visit(TupleExprAST* ast)    { currentRoot->append(ast); } 
void BuildCFG::visit(BuiltinCompilesExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(NamedTypeDeclAST* ast) { currentRoot->append(ast); }

void BuildCFG::visit(SeqAST* ast)  { absorb(this, ast->parts); }
void BuildCFG::visit(CallAST* ast) { absorb(this, ast->parts); }

void BuildCFG::visit(PrototypeAST* ast) {
  // skip
}

void BuildCFG::visit(ModuleAST* ast)              {
  for (ModuleAST::FnAST_iterator
       it  = ast->fn_begin();
       it != ast->fn_end(); ++it) {
    (*it)->accept(this);
  }
}

void BuildCFG::visit(IfExprAST* ast) {
  /*
  // Does the standard thing, pretty much:
  //
  //        BEFORE                           AFTER
  //        ======                           =====
  //    +------------+                  +------------+
  //    |            |                  |            |
  //    |    this    |                  |            |
  //    |currentRoot |                  |    root    |
  //    |............|                  |     cond   |
  //    +            +                  +------_--_--+
  //                                        _,'    `-.
  //                                     ,,'          `-.
  //                                ...,:__           ___;,._,._
  //                            /--P      .\._     ,_/|      '  \
  //                           _\.            '\   | '          /
  //                          |               `".  `=.          `|
  //                          './-   then        | |     else   ,'
  //                           /              Y--' ./"`         \'
  //                          |. .    ..  | ../    '.....   , .o'
  //                            ''\.../ `'-.          ,,'--'
  //                                        `._   ,,-'
  //                                     +-------'----+
  //                                     |            |
  //                                     |   current  |
  //                                     |            |
  //                                     |............|
  //                                     +            +
   */

  ast->getTestExpr()->accept(this);
  CFG* root = currentRoot;

  CFG* thenCFGroot = new CFG("if.then", ast->getThenExpr(), currentFn);
  CFG* elseCFGroot = new CFG("if.else", ast->getElseExpr(), currentFn);

  this->currentRoot = thenCFGroot;
  ast->getThenExpr()->accept(this);
  CFG* thenCFGtail = this->currentRoot;

  this->currentRoot = elseCFGroot;
  ast->getElseExpr()->accept(this);
  CFG* elseCFGtail = this->currentRoot;

  this->currentRoot = new CFG("if.cont", ast->parent, currentFn);

  // Connect the CFGs
  root->branchCond(ast->getTestExpr(), thenCFGroot, elseCFGroot);

  thenCFGtail->branchTo(currentRoot);
  elseCFGtail->branchTo(currentRoot);
}

void BuildCFG::visit(ForRangeExprAST* ast) {

  /* Generate the following CFG structure:
  preLoopBB:
        ...
        br loopHdrBB

  loopHdrBB:
        incr = incrExpr
        end = endExpr
        sv = startExpr
        precond = sv < end
        br precond? loopBB afterBB

  loopBB:
        loopvar = phi...
        body
        ...

  loopEndBB:
        ...
        next = loopvar + 1

        cond = next < end
        br cond? loopBB afterBB

  afterBB:
        ...
   */

  CFG* loopHdr = new CFG("forToHdr", ast, currentFn);

  std::cout << "current fn is " << this->currentFn->getProto()->name
      << ", forToHdr: " << loopHdr << ", for range:" << ast << " => " << str(ast) << std::endl;
  CFG* loop    = new CFG("forTo",    ast, currentFn);
  CFG* loopEnd = new CFG("forToEnd", ast, currentFn);
  CFG* after   = new CFG("postloop", ast, currentFn);

  CFG* preLoop = currentRoot;

  ast->getIncrExpr()->accept(this);

  currentRoot = loopHdr;
  ast->getEndExpr()->accept(this);
  ast->getStartExpr()->accept(this);
  CFG* endStart = currentRoot;

  currentRoot = loop;
  ast->getBodyExpr()->accept(this);
  CFG* endBody = currentRoot;

  currentRoot = after;

  preLoop->branchTo(loopHdr);
  endBody->branchTo(loopEnd);
  endStart->branchCond(NULL, loop, after);
  loopEnd->branchCond(NULL, loop, after);
}

void BuildCFG::visit(FnAST* ast) {
  currentFn   = ast;
  currentRoot = new CFG(ast->getProto()->name + std::string(".entry"),
                        ast, currentFn);
  ast->getBody()->accept(this);
}



