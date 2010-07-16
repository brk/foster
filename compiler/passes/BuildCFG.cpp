// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "parse/FosterAST.h"

#include "passes/BuildCFG.h"

using foster::SourceRange;
using foster::EDiag;
using foster::show;
using foster::CFG;

void absorb(BuildCFG* pass, Exprs& exprs) {
  for (Exprs::iterator it = exprs.begin(); it != exprs.end(); ++it) {
    ExprAST* ast = (*it);
    ast->accept(pass);
  }
}

void BuildCFG::visit(IntAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(BoolAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(VariableAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(UnaryOpExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(BinaryOpExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(NilExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(RefExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(DerefExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(AssignExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(SubscriptAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(ClosureAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(ArrayExprAST* ast) { currentRoot->append(ast); }
void BuildCFG::visit(SimdVectorAST* ast) { currentRoot->append(ast); } 
void BuildCFG::visit(TupleExprAST* ast) { currentRoot->append(ast); } 
void BuildCFG::visit(BuiltinCompilesExprAST* ast) { currentRoot->append(ast); }

void BuildCFG::visit(SeqAST* ast) { absorb(this, ast->parts); }
void BuildCFG::visit(CallAST* ast) { absorb(this, ast->parts); }

void BuildCFG::visit(PrototypeAST* ast) {
  // skip
}

void BuildCFG::visit(ModuleAST* ast)              {
  for (size_t i = 0; i < ast->functions.size(); ++i) {
    ast->functions[i]->accept(this);
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

  ast->testExpr->accept(this);
  CFG* root = currentRoot;

  CFG* thenCFGroot = new CFG("if.then", ast->thenExpr);
  CFG* elseCFGroot = new CFG("if.else", ast->elseExpr);

  this->currentRoot = thenCFGroot;
  ast->thenExpr->accept(this);
  CFG* thenCFGtail = this->currentRoot;

  this->currentRoot = elseCFGroot;
  ast->elseExpr->accept(this);
  CFG* elseCFGtail = this->currentRoot;

  this->currentRoot = new CFG("if.cont", ast->parent);

  // Connect the CFGs
  root->branchCond(ast->testExpr, thenCFGroot, elseCFGroot);

  thenCFGtail->branchTo(currentRoot);
  elseCFGtail->branchTo(currentRoot);

  currentFn->cfgs.push_back(thenCFGroot);
  currentFn->cfgs.push_back(elseCFGroot);
  currentFn->cfgs.push_back(currentRoot);
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

  CFG* loopHdr = new CFG("forToHdr", ast);

  std::cout << "current fn is " << this->currentFn->proto->name
      << ", forToHdr: " << loopHdr << ", for range:" << ast << " => " << str(ast) << std::endl;
  CFG* loop    = new CFG("forTo",    ast);
  CFG* loopEnd = new CFG("forToEnd", ast);
  CFG* after   = new CFG("postloop", ast);

  CFG* preLoop = currentRoot;

  if (ast->incrExpr) {
    ast->incrExpr->accept(this);
  } else {
    (new IntAST("1", "1", SourceRange::getEmptyRange()))->accept(this);
  }

  currentRoot = loopHdr;
  ast->endExpr->accept(this);
  ast->startExpr->accept(this);
  CFG* endStart = currentRoot;

  currentRoot = loop;
  ast->bodyExpr->accept(this);
  CFG* endBody = currentRoot;

  currentRoot = after;

  preLoop->branchTo(loopHdr);
  endBody->branchTo(loopEnd);
  endStart->branchCond(NULL, loop, after);
  loopEnd->branchCond(NULL, loop, after);

  currentFn->cfgs.push_back(loopHdr);
  currentFn->cfgs.push_back(loop);
  currentFn->cfgs.push_back(loopEnd);
  currentFn->cfgs.push_back(after);
}

void BuildCFG::visit(FnAST* ast) {
  currentRoot = new CFG(ast->proto->name + std::string(".entry"), ast);
  currentFn   = ast;
  currentFn->cfgs.push_back(currentRoot);

  ast->body->accept(this);
}



