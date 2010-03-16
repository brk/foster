// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "PrettyPrintPass.h"
#include "FosterAST.h"
#include <cassert>

////////////////////////////////////////////////////////////////////

std::string str(const llvm::Type* ty) {
  std::stringstream ss; ss << *ty; return ss.str();
}

void PrettyPrintPass::visit(BoolAST* ast) {
  scan(PPToken( (ast->boolValue) ? "true" : "false" ));
}

void PrettyPrintPass::visit(IntAST* ast) {
  scan(PPToken(ast->Text));
}

// name (: type)
void PrettyPrintPass::visit(VariableAST* ast) {
  scan(PPToken(ast->name));
  if (this->printVarTypes) {
    scan(PPToken(":"));
    /*if (ast->tyExpr) {
      ast->tyExpr->accept(this);
    } else*/ if (ast->type) {
      std::stringstream ss; ss << *(ast->type);
      scan(PPToken(ss.str()));
    }
  }
}

void PrettyPrintPass::visit(UnaryOpExprAST* ast) {
  scan(PPToken(ast->op));
  scan(PPToken(" "));
  ast->parts[0]->accept(this);
}

// $0 op $1
void PrettyPrintPass::visit(BinaryOpExprAST* ast) {
  scan(tBlockOpen);
  ast->parts[0]->accept(this);
  scan(PPToken(" "));
  scan(PPToken(ast->op));
  scan(PPToken(" "));
  ast->parts[1]->accept(this);
  scan(tBlockClose);
}

// fn Name (inArgs to outArgs)
void PrettyPrintPass::visit(PrototypeAST* ast) {
  //scan(tBlockOpen);
  //scan(tBlockOpen);
  scan(PPToken("fn"));
  scan(PPToken(" "));
  scan(PPToken(ast->name));
  scan(PPToken(" "));
  //scan(tBlockClose);
  //scan(tBlockOpen);
  scan(PPToken("("));
  for (int i = 0; i < ast->inArgs.size(); ++i) {
    scan(PPToken(" "));
    this->printVarTypes = true;
    ast->inArgs[i]->accept(this);
    this->printVarTypes = false;
  }
  if (ast->resultTy != NULL) {
    scan(PPToken(" to "));
    scan(PPToken(str(ast->resultTy)));
  }
  scan(PPToken(" "));
  scan(PPToken(")"));
  //scan(tBlockClose);
  //scan(tBlockClose);
}

// fnProto fnBody
void PrettyPrintPass::visit(FnAST* ast) {
  bool isTopLevelFn = ast->parent->parent == NULL;
  if (isTopLevelFn) { scan(tNewline); }
  ast->proto->accept(this);
  ast->body->accept(this);
  if (isTopLevelFn) { scan(tNewline); }
}


void PrettyPrintPass::visit(ClosureTypeAST* ast) {
  scan(PPToken("<TyClosure "));
  scan(PPToken(str(ast->proto->type)));
  scan(PPToken(">"));
}

void PrettyPrintPass::visit(ClosureAST* ast) {
  scan(PPToken("<closure "));
  if (ast->fn) {
    scan(PPToken(str(ast->fn->proto->type)));
  }
  scan(PPToken(">"));
}

// if $0 { $1 } else { $2 }
void PrettyPrintPass::visit(IfExprAST* ast) {
  //scan(tBlockOpen);
  scan(PPToken("if "));
  //ast->parts[0]->accept(this);
  ast->testExpr->accept(this);
  //scan(tBlockClose);
  
  scan(PPToken(" "));
  scan(tOptNewline);
  
  //ast->parts[1]->accept(this);
  ast->thenExpr->accept(this);
  
  scan(PPToken(" else "));
  scan(tOptNewline);
  
  ast->elseExpr->accept(this);
  //ast->parts[2]->accept(this);
}

// $0 [ $1 ]
void PrettyPrintPass::visit(SubscriptAST* ast) {
  //scan(tBlockOpen);
  ast->parts[0]->accept(this);
  
  scan(PPToken("["));
  ast->parts[1]->accept(this);
  scan(PPToken("]"));
  //scan(tBlockClose);
}

// { $0 ; $1 ; ... ; $n }
void PrettyPrintPass::visit(SeqAST* ast) {
  scan(tBlockOpen);
  scan(tIndent);
  FnAST* followingFn = dynamic_cast<FnAST*>(ast->parent);
  if (followingFn) {
    scan(PPToken(" {"));
    scan(tNewline);
  } else {
    scan(PPToken("{ "));
  }

  for (int i = 0; i < ast->parts.size(); ++i) {
    ast->parts[i]->accept(this);
    
    if (i != ast->parts.size() - 1) {
      if (CallAST* wasCall = dynamic_cast<CallAST*>(ast->parts[i])) {
        scan(tNewline);
      } else {
        scan(PPToken("; "));
      }
    }
  }

  scan(tDedent);

  if (followingFn) {
    scan(tNewline);
    scan(PPToken("}"));
  } else {
    scan(PPToken(" }"));
  }

  scan(tBlockClose);
}

// $0 ( $1, $2, ... , $n )
void PrettyPrintPass::visit(CallAST* ast) {
  scan(tBlockOpen);
  ast->parts[0]->accept(this);
  
  scan(PPToken("("));

  if (ast->parts.size() > 1) {
    scan(tIndent);
  }

  bool first = true;
  for (int i = 1; i < ast->parts.size(); ++i) {
    if (!first) {
      scan(PPToken(","));
      scan(PPToken(" "));
    }
    first = false;

    if (i == ast->parts.size() -1) {
      // dedent "early" because a dedent followed directly
      // by a close-paren doesn't do much for us...
      scan(tDedent);
    }

    ast->parts[i]->accept(this);
  }

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


// simd-vector $0
void PrettyPrintPass::visit(SimdVectorAST* ast) {
  scan(PPToken("simd-vector"));
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
  if (ast->parts[0]) {
      ast->parts[0]->accept(this);
  } else {
      scan(PPToken("<nil>")); 
  }
  //scan(tBlockClose);
}

