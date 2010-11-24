// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/FosterTypeAST.h"
#include "parse/ExprASTVisitor.h"
#include "parse/TypeASTVisitor.h"
#include "base/Diagnostics.h"
#include "parse/ParsingContext.h"

using namespace foster;

bool compareTypeASTs(TypeAST* good, TypeAST* bad);

struct ExprASTDiff : public ExprASTVisitor {
  ExprASTDiff(ExprAST* ast) {
    bads.push_back(ast);
    differed = false;
  }
  ExprAST* getBad() { return bads.back(); }
  ExprAST* setBad(ExprAST* ast) { bads.back() = ast; }

  bool differed;
  std::vector<ExprAST*> bads;

  template <typename T>
  T* sanityCheck(T* ast) {
    if (std::string(getBad()->tag) != std::string(ast->tag)) {
      err() << "\t" << ast << " // " << getBad() << "\n";
      err() << "Mismatch " << ast->tag << " vs " << getBad()->tag << "\n";
      err() << "\n\t" << str(ast)
            << "\n\t" << str(getBad());
    } else if (compareTypeASTs(ast->type, getBad()->type)) {
      err() << "Sanity check on expr failed, types differ!" << "\n";
      return NULL;
    } else {
      return dynamic_cast<T*>(getBad());
    }
  }

  llvm::raw_ostream& err() {
    differed = true;
    return llvm::errs();
  }

  void visitChildren(ExprAST* ast) {
    ExprAST* bad = getBad();
    for (size_t i = 0; i < ast->parts.size(); ++i) {
      if (ast->parts[i] && bad->parts[i]) {
        setBad(bad->parts[i]);
        this->onVisitChild(ast, ast->parts[i]);
      } else if (!ast->parts[i]) {
        EDiag() << "visitChildren saw null part " << i << " for ast node " << str(ast) << show(ast);
      } else if (!bad->parts[i]) {
        EDiag() << "visitChildren saw null part " << i << " for bad node " << str(bad) << show(bad);
      }
    }
  }

  void visit(PrototypeAST* ast);
  void visit(BoolAST* ast);
  void visit(IntAST* ast);
  void visit(FnAST* ast);
  void visit(CallAST* ast);
  void visit(BuiltinCompilesExprAST* ast);
  void visit(IfExprAST* ast);
  void visit(TupleExprAST* ast);
  void visit(ModuleAST* ast);
  void visit(SeqAST* ast);
  void visit(NilExprAST* ast);
  void visit(SubscriptAST* ast);
  void visit(NamedTypeDeclAST* ast);
  void visit(VariableAST* ast);
};

namespace foster {
  bool compareExprASTs(ExprAST* good, ExprAST* bad) {
    if (!good && !bad) return false;

    ExprASTDiff d(bad); good->accept(&d);
    return d.differed;
  }
}

////////////////////////////////////////////////////////////////////

void ExprASTDiff::visit(BoolAST* ast)                {
  if (BoolAST* ibad = sanityCheck(ast)) {
    if (ibad->boolValue != ast->boolValue) {
      err() << "BoolAST boolValue mismatch" << "\n";
    }
  }
  llvm::outs() << "ExprASTDiff::BoolAST ok" << "\n";
}
void ExprASTDiff::visit(IntAST* ast)                 {
  if (IntAST* ibad = sanityCheck(ast)) {
    if (ibad->getOriginalText() != ast->getOriginalText()) {
      err() << "Int getOriginalText mismatch" << "\n";
    }
    if (ibad->getBase() != ast->getBase()) {
      err() << "Int getBase mismatch" << "\n";
    }
  }
  llvm::outs() << "ExprASTDiff::IntAST ok" << "\n";
}
void ExprASTDiff::visit(VariableAST* ast)                {
  if (VariableAST* ibad = sanityCheck(ast)) {
    if (ibad->getName() != ast->getName()) {
      err() << "VariableAST getName mismatch" << "\n";
    }
  }
  llvm::outs() << "ExprASTDiff::VariableAST ok" << "\n";
}
void ExprASTDiff::visit(NilExprAST* ast)             { return; }
void ExprASTDiff::visit(NamedTypeDeclAST* ast)       { return; }

// Just recurse...
// (the |if (0)|s are because some types visit children in their ->accept() implementations.
void ExprASTDiff::visit(ModuleAST* ast)              {
  if (ModuleAST* ibad = sanityCheck(ast)) {
    this->visitChildren(ast);
  }
  llvm::outs() << "ExprASTDiff::ModuleAST ok" << "\n";
}
void ExprASTDiff::visit(IfExprAST* ast)              {
  if (IfExprAST* ibad = sanityCheck(ast)) {
    this->visitChildren(ast);
  }
  llvm::outs() << "ExprASTDiff::IfExprAST ok" << "\n";
}
void ExprASTDiff::visit(SubscriptAST* ast)           { if (0) this->visitChildren(ast); }
void ExprASTDiff::visit(SeqAST* ast)                 { if (0) this->visitChildren(ast); }
void ExprASTDiff::visit(CallAST* ast)                {
  if (CallAST* ibad = sanityCheck(ast)) {
    this->visitChildren(ast);
  }
  llvm::outs() << "ExprASTDiff::CallAST ok" << "\n";
}
void ExprASTDiff::visit(TupleExprAST* ast)           { if (0) this->visitChildren(ast); }
void ExprASTDiff::visit(BuiltinCompilesExprAST* ast) {
  if (BuiltinCompilesExprAST* ibad = sanityCheck(ast)) {
    if (ibad->status != ast->status) {
      err() << "_BuiltinCompilesExprAST status mismatch; "
            << ibad->status << " vs " << ast->status << "\n";
    } else {
      this->visitChildren(ast);
    }
  }
  llvm::outs() << "ExprASTDiff::BuiltinCompiles ok" << "\n";
}

void ExprASTDiff::visit(FnAST* ast) {
  if (FnAST* ibad = sanityCheck(ast)) {
    if (!ibad->scope && ast->scope) {
      err() << "FnAST lacks scope" << "\n";
    } else if (ibad->isClosure() != ast->isClosure()) {
      err() << "FnAST isClosure mismatch" << "\n";
    } else if (ast->isClosure()) {
      // TODO check env parts
      /*
      for (size_t i = 0; i < ast->environmentParts->size(); ++i) {
        onVisitChild(ast, (*(ast->environmentParts))[i]);
      }
    */
    } else {
      setBad(ibad->proto);
      onVisitChild(ast, ast->proto);
      setBad(ibad->getBody());
      onVisitChild(ast, ast->getBody());
    }
  }

  llvm::outs() << "ExprASTDiff::FnAST ok" << "\n";
}

void ExprASTDiff::visit(PrototypeAST* ast)           {
  if (PrototypeAST* ibad = sanityCheck(ast)) {
    if (ast->inArgs.size() != ibad->inArgs.size()) {
      err() << "PrototypeAST inArgs size mismatch" << "\n";
    } else {
      for (size_t i = 0; i < ast->inArgs.size(); ++i) {
        setBad(ibad->inArgs[i]);
        onVisitChild(ast, ast->inArgs[i]);
      }
      if (compareTypeASTs(ast->resultTy, ibad->resultTy)) {
        err() << "PrototypeAST resultTy differs" << "\n";
      }
    }
  }
  llvm::outs() << "ExprASTDiff::PrototypeAST ok" << "\n";
}

/////////////////////////////////////////////

struct TypeASTDiff : public TypeASTVisitor {
  TypeAST* bad;
  bool differed;
  TypeASTDiff(TypeAST* bad) : bad(bad), differed(false) {}

  template <typename T>
  T* sanityCheck(T* ast) {
    if (std::string(bad->tag) != std::string(ast->tag)) {
      err() << "Type mismatch " << ast->tag << " vs " << bad->tag << "\n";
      err() << "\n\t" << str(ast)
            << "\n\t" << str(bad) << "\n";
      return NULL;
    } else {
      return dynamic_cast<T*>(bad);
    }
  }

  llvm::raw_ostream& err() {
    differed = true;
    return llvm::errs();
  }

  virtual void visitChildren(TypeAST* ast) {
    // Only visit children manually!
  }

  #include "parse/TypeASTVisitor.decls.inc.h"
};

// returns true if types differed
bool compareTypeASTs(TypeAST* good, TypeAST* bad) {
  if (!good && !bad) return false;

  if (good && !bad) {
    llvm::errs() << "Had unexpected NULL 'bad' type AST when comparing." << "\n";
    return true;
  }
  TypeASTDiff d(bad);
  good->accept(&d);
  return d.differed;
}

void TypeASTDiff::visit(NamedTypeAST* ast) {
  if (NamedTypeAST* ibad = sanityCheck(ast)) {
    if (ibad->getName() != ast->getName()) {
      err() << ast->tag << " " << ast->getName()
        << " vs " << ibad->getName() << "\n";
    }
    // check nonLLVMType?
  }
}

void TypeASTDiff::visit(TypeVariableAST* ast) {
  if (TypeVariableAST* ibad = sanityCheck(ast)) {
    if (ibad->getTypeVariableName()
      != ast->getTypeVariableName()) {
    err() << ast->tag << " : getTypeVariableName: "
                   << ast->getTypeVariableName()
        << " vs " << ibad->getTypeVariableName() << "\n";
    }
    // check nonLLVMType?
  }
}

void TypeASTDiff::visit(FnTypeAST* ast) {
  if (FnTypeAST* ibad = sanityCheck(ast)) {
    if (ibad->getCallingConventionID()
       != ast->getCallingConventionID()) {
      err() << "FnTypeAST calling conventions differed" << "\n";
    } else if (!ibad->getReturnType()
      &&  ast->getReturnType()) {
      err() << "FnTypeAST had null return type" << "\n";
    } else if (ibad->getNumParams()
             != ast->getNumParams()) {
      err() << "FnTypeAST had wrong number of params" << "\n";
    } else if (compareTypeASTs(ibad->getReturnType(),
                                ast->getReturnType())) {
      err() << "FnTypeAST return types differed" << "\n";
    } else {
      for (int i = 0; i < ast->getNumParams(); ++i) {
        bool diff = compareTypeASTs(
                ibad->getParamType(i),
                 ast->getParamType(i));
        if (diff) {
          err() << "FnTypeAST arg types differed" << "\n";
          break;
        }
      }
    }
  }
}

void TypeASTDiff::visit(RefTypeAST* ast) {
  if (RefTypeAST* ibad = sanityCheck(ast)) {
    if (!ibad->getElementType()) {
      err() << "RefType had null element type" << "\n";
    } else {
      this->differed = compareTypeASTs(
                ibad->getElementType(),
                 ast->getElementType());
    }
  }
}

void TypeASTDiff::visit(TupleTypeAST* ast) {
  if (TupleTypeAST* ibad = sanityCheck(ast)) {
    if (ibad->getNumContainedTypes() !=
         ast->getNumContainedTypes()) {
      err() << "Tuple types of different size" << "\n";
    } else {
      for (int i = 0; i < ast->getNumContainedTypes(); ++i) {
        bool diff = compareTypeASTs(
                ibad->getContainedType(i),
                 ast->getContainedType(i));
        if (diff) {
          this->differed = true; break;
        }
      }
    }
  }
}

