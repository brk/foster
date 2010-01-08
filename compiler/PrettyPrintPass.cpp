// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "PrettyPrintPass.h"
#include "FosterAST.h"

////////////////////////////////////////////////////////////////////

void PrettyPrintPass::visit(BoolAST* ast) {
  scan(PPToken( (ast->boolValue) ? "true" : "false" ));
}

void PrettyPrintPass::visit(IntAST* ast) {
  scan(PPToken(ast->Text));
}

// name (: type)
void PrettyPrintPass::visit(VariableAST* ast) {
  scan(PPToken(ast->Name));
  if (false && ast->tyExpr) {
    scan(PPToken(":"));
    ast->tyExpr->accept(this);
  }
}

// $0 op $1
void PrettyPrintPass::visit(BinaryOpExprAST* ast) {
  ////scan(tBlockOpen);
  ast->parts[0]->accept(this);
  scan(PPToken(" "));
  scan(PPToken(ast->op));
  scan(PPToken(" "));
  ast->parts[1]->accept(this);
  ////scan(tBlockClose);
}

// fn Name (inArgs to outArgs)
void PrettyPrintPass::visit(PrototypeAST* ast) {
  //scan(tBlockOpen);
  //scan(tBlockOpen);
  scan(PPToken("fn"));
  scan(PPToken(" "));
  scan(PPToken(ast->Name));
  scan(PPToken(" "));
  //scan(tBlockClose);
  //scan(tBlockOpen);
  scan(PPToken("("));
  for (int i = 0; i < ast->inArgs.size(); ++i) {
    scan(PPToken(" "));
    scan(PPToken(ast->inArgs[i]->Name));
  }
  if (!ast->outArgs.empty()) {
    scan(PPToken(" "));
    scan(PPToken("to"));
    for (int i = 0; i < ast->outArgs.size(); ++i) {
      scan(PPToken(" "));
      scan(PPToken(ast->outArgs[i]->Name));
    }
  }
  scan(PPToken(" "));
  scan(PPToken(")"));
  //scan(tBlockClose);
  //scan(tBlockClose);
}

// fnProto fnBody
void PrettyPrintPass::visit(FnAST* ast) {
  ast->Proto->accept(this);
  scan(PPToken(" "));
  ast->Body->accept(this);
}

// if $0 { $1 } else { $2 }
void PrettyPrintPass::visit(IfExprAST* ast) {
  //scan(tBlockOpen);
  scan(PPToken("if"));
  scan(PPToken(" "));
  //ast->parts[0]->accept(this);
  ast->ifExpr->accept(this);
  //scan(tBlockClose);
  
  scan(PPToken(" "));
  
  //ast->parts[1]->accept(this);
  ast->thenExpr->accept(this);
  
  scan(PPToken(" "));
  scan(PPToken("else"));
  scan(PPToken(" "));
  
  ast->elseExpr->accept(this);
  //ast->parts[2]->accept(this);
}

// $0 [ $1 ]
void PrettyPrintPass::visit(SubscriptAST* ast) {
  //scan(tBlockOpen);
  ast->parts[0]->accept(this);
  
  scan(PPToken(" "));
  scan(PPToken("["));
  scan(PPToken(" "));
  ast->parts[1]->accept(this);
  
  scan(PPToken(" "));
  scan(PPToken("]"));
  //scan(tBlockClose);
}

// { $0 ; $1 ; ... ; $n }
void PrettyPrintPass::visit(SeqAST* ast) {
  scan(tBlockOpen);
  scan(PPToken("{"));
  scan(PPToken(" "));
  bool first = true;
  for (int i = 0; i < ast->parts.size(); ++i) {
    if (!first) {
      scan(PPToken(";"));
      scan(PPToken(" ", true));
      /*
      if (CallAST* wasCall = dynamic_cast<CallAST*>(ast->parts[i-1])) {
        scan(PPToken("\n"));
      } else {
        scan(PPToken(" "));
      }
      */
    }
    first = false;
    ast->parts[i]->accept(this);
    scan(PPToken(" "));
  }
  scan(PPToken("}"));
  scan(tBlockClose);
}

// $0 ( $1, $2, ... , $n )
void PrettyPrintPass::visit(CallAST* ast) {
  scan(tBlockOpen);
  ast->parts[0]->accept(this);
  
  scan(PPToken(" "));
  scan(PPToken("("));
  scan(PPToken(" "));
  bool first = true;
  for (int i = 1; i < ast->parts.size(); ++i) {
    if (!first) {
      scan(PPToken(","));
      scan(PPToken(" "));
    }
    first = false;
    ast->parts[i]->accept(this);
  }
  scan(PPToken(" "));
  scan(PPToken(")"));
  scan(tBlockClose);
}
// array $0
void PrettyPrintPass::visit(ArrayExprAST* ast) {
  scan(PPToken("array"));
  scan(PPToken(" "));
  if (ast->parts[0]) {
    ast->parts[0]->accept(this);
  } else {
    scan(PPToken("<nil>"));  
  }
}

// tuple $0
void PrettyPrintPass::visit(TupleExprAST* ast) {
  scan(PPToken("tuple"));
  scan(PPToken(" "));
  if (ast->parts[0]) {
    ast->parts[0]->accept(this);
  } else {
    scan(PPToken("<nil>"));
  }
}

// unpack $0
void PrettyPrintPass::visit(UnpackExprAST* ast) {
  scan(PPToken("unpack"));
  scan(PPToken(" "));
  ast->parts[0]->accept(this);
}

// __COMPILES__ $0
void PrettyPrintPass::visit(BuiltinCompilesExprAST* ast) {
  //scan(tBlockClose);
  scan(PPToken("__COMPILES__"));
  scan(PPToken(" "));
  ast->parts[0]->accept(this);
  //scan(tBlockClose);
}

