// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "PrettyPrintPass.h"
#include "FosterAST.h"

////////////////////////////////////////////////////////////////////

void PrettyPrintPass::visit(BoolAST* ast) {
  scan(PPToken_from( (ast->boolValue) ? "true" : "false" ));
}

void PrettyPrintPass::visit(IntAST* ast) {
  scan(PPToken_from(ast->Text));
}

// name (: type)
void PrettyPrintPass::visit(VariableAST* ast) {
  scan(PPToken_from(ast->Name));
  if (false && ast->tyExpr) {
    scan(PPToken_from(":"));
    ast->tyExpr->accept(this);
  }
}

// $0 op $1
void PrettyPrintPass::visit(BinaryOpExprAST* ast) {
  ////scan(tBlockOpen);
  ast->parts[0]->accept(this);
  scan(PPToken_from(ast->op));
  ast->parts[1]->accept(this);
  ////scan(tBlockClose);
}

// fn Name (inArgs to outArgs)
void PrettyPrintPass::visit(PrototypeAST* ast) {
  //scan(tBlockOpen);
  //scan(tBlockOpen);
  scan(PPToken_from("fn"));
  scan(PPToken_from(" "));
  scan(PPToken_from(ast->Name));
  scan(PPToken_from(" "));
  //scan(tBlockClose);
  //scan(tBlockOpen);
  scan(PPToken_from("("));
  for (int i = 0; i < ast->inArgs.size(); ++i) {
    scan(PPToken_from(" "));
    scan(PPToken_from(ast->inArgs[i]->Name));
  }
  if (!ast->outArgs.empty()) {
    scan(PPToken_from(" "));
    scan(PPToken_from("to"));
    for (int i = 0; i < ast->outArgs.size(); ++i) {
      scan(PPToken_from(" "));
      scan(PPToken_from(ast->outArgs[i]->Name));
    }
  }
  scan(PPToken_from(" "));
  scan(PPToken_from(")"));
  //scan(tBlockClose);
  //scan(tBlockClose);
}

// fnProto fnBody
void PrettyPrintPass::visit(FnAST* ast) {
  ast->Proto->accept(this);
  scan(PPToken_from(" "));
  ast->Body->accept(this);
}

// if $0 { $1 } else { $2 }
void PrettyPrintPass::visit(IfExprAST* ast) {
  //scan(tBlockOpen);
  scan(PPToken_from("if"));
  scan(PPToken_from(" "));
  //ast->parts[0]->accept(this);
  ast->ifExpr->accept(this);
  //scan(tBlockClose);
  
  //ast->parts[1]->accept(this);
  ast->thenExpr->accept(this);
  
  scan(PPToken_from(" "));
  scan(PPToken_from("else"));
  scan(PPToken_from(" "));
  
  ast->elseExpr->accept(this);
  //ast->parts[2]->accept(this);
}

// $0 [ $1 ]
void PrettyPrintPass::visit(SubscriptAST* ast) {
  //scan(tBlockOpen);
  ast->parts[0]->accept(this);
  
  scan(PPToken_from(" "));
  scan(PPToken_from("["));
  scan(PPToken_from(" "));
  ast->parts[1]->accept(this);
  
  scan(PPToken_from(" "));
  scan(PPToken_from("]"));
  //scan(tBlockClose);
}

// { $0 ; $1 ; ... ; $n }
void PrettyPrintPass::visit(SeqAST* ast) {
  scan(tBlockOpen);
  scan(PPToken_from("{"));
  scan(PPToken_from(" "));
  bool first = true;
  for (int i = 0; i < ast->parts.size(); ++i) {
    if (!first) {
      scan(PPToken_from(";"));
      scan(PPToken_from(" "));
    }
    first = false;
    ast->parts[i]->accept(this);
    scan(PPToken_from(" "));
  }
  scan(PPToken_from("}"));
  scan(tBlockClose);
}

// $0 ( $1, $2, ... , $n )
void PrettyPrintPass::visit(CallAST* ast) {
  //scan(tBlockOpen);
  ast->parts[0]->accept(this);
  
  scan(PPToken_from(" "));
  scan(PPToken_from("("));
  scan(PPToken_from(" "));
  bool first = true;
  for (int i = 1; i < ast->parts.size(); ++i) {
    if (!first) {
      scan(PPToken_from(","));
      scan(PPToken_from(" "));
    }
    first = false;
    ast->parts[i]->accept(this);
  }
  scan(PPToken_from(" "));
  scan(PPToken_from(")"));
  //scan(tBlockClose);
}

// array $0
void PrettyPrintPass::visit(ArrayExprAST* ast) {
  scan(PPToken_from("array"));
  scan(PPToken_from(" "));
  if (ast->parts[0]) {
    ast->parts[0]->accept(this);
  } else {
    scan(PPToken_from("<nil>"));  
  }
}

// tuple $0
void PrettyPrintPass::visit(TupleExprAST* ast) {
  scan(PPToken_from("tuple"));
  scan(PPToken_from(" "));
  if (ast->parts[0]) {
    ast->parts[0]->accept(this);
  } else {
    scan(PPToken_from("<nil>"));
  }
}

// unpack $0
void PrettyPrintPass::visit(UnpackExprAST* ast) {
  scan(PPToken_from("unpack"));
  scan(PPToken_from(" "));
  ast->parts[0]->accept(this);
}

// __COMPILES__ $0
void PrettyPrintPass::visit(BuiltinCompilesExprAST* ast) {
  //scan(tBlockClose);
  scan(PPToken_from("__COMPILES__"));
  scan(PPToken_from(" "));
  ast->parts[0]->accept(this);
  //scan(tBlockClose);
}

