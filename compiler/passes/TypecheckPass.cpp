// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "TypecheckPass.h"
#include "FosterAST.h"
#include "FosterUtils.h"

#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/ADT/APInt.h"

using llvm::Type;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;

#include <vector>
#include <map>
#include <cassert>

using std::vector;

////////////////////////////////////////////////////////////////////

void TypecheckPass::visit(BoolAST* ast) {
  ast->type = TypeAST::get(LLVMTypeFor("i1"));
}

const Type* LLVMintTypeForNBits(unsigned n) {
  // Disabled until we get better inferred literal types
  //if (n <= 1) return LLVMTypeFor("i1");
  //if (n <= 8) return LLVMTypeFor("i8");
  //if (n <= 16) return LLVMTypeFor("i16");
  if (n <= 32) return LLVMTypeFor("i32");
  if (n <= 64) return LLVMTypeFor("i64");
}

void TypecheckPass::visit(IntAST* ast) {
  // Make sure the base is a reasonable one
  if (!(ast->Base == 2  || ast->Base == 8
     || ast->Base == 10 || ast->Base == 16)) {
    return;
  }

  // Make sure the literal only contains
  // valid digits for the chosen base.
  const char* digits = "0123456789abcdef";
  for (int i = 0; i < ast->Clean.size(); ++i) {
    char c = tolower(ast->Clean[i]);
    ptrdiff_t pos = std::find(digits, digits + 16, c) - digits;
    if (pos >= ast->Base) {
      return;
    }
  }

  // Start with a very conservative estimate of how
  // many bits we need to represent this integer
  int bitsPerDigit = int(ceil(log(ast->Base)/log(2)));
  int conservativeBitsNeeded = bitsPerDigit * ast->Clean.size();
  APInt n(conservativeBitsNeeded, ast->Clean, ast->Base);
  unsigned activeBits = n.getActiveBits();
  if (activeBits > 32) {
    std::cerr << "Integer literal '" << ast->Text << "' requires "
              << activeBits << " bits to represent." << std::endl;
    return;
  } else {
#   if 0
      std::cerr << "Integer literal '" << ast->Text << "' requires "
                  << activeBits << " bits to represent." << std::endl;
#   endif
  }

  ast->type = TypeAST::get(LLVMintTypeForNBits(activeBits));
}

void TypecheckPass::visit(VariableAST* ast) {
  if (this->typeParsingMode) {
    ast->type = TypeASTFor(ast->name);
#if 1
    std::cout << "visited var " << ast->name << " in type parsing mode;"
	" ast->type is " << str(ast->type)
	<< "; tyExpr = " << str(ast->tyExpr)
	<< "; llType = " << str(LLVMTypeFor(ast->name))
	<< std::endl;
#endif
  }

  if (!ast->tyExpr) {
    if (!ast->type) {
      // Eventually we should do local type inference...
      std::cerr << "Error: typechecking variable " << ast->name << " <"<< ast <<"> with no type provided! " << std::endl;
    }
    return;
  }

  if (ast->tyExpr && ast->type) {
    /*
    if (ast->tyExpr->type != ast->type) {
      std::cerr << "Error: typechecking variable " << ast->name << " with both type expr ";
      std::cerr << std::endl << "\t" << *(ast->tyExpr);
      std::cerr << " and type constant "
                << std::endl << "\t" << *(ast->type) << std::endl;
    }
    */
    return;
  }

  // Extract an llvm::Type from the type expression; typeParsingMode
  // causes names to be interpreted directly as type names, rather than
  // variable names.
  //std::cerr << "Parsing type for expr " << *(ast->tyExpr) << std::endl;
  TypecheckPass typeParsePass; typeParsePass.typeParsingMode = true;
  ast->tyExpr->accept(&typeParsePass);
  ast->type = ast->tyExpr->type;

  //std::cerr << "Parsed type as " << (ast->type) << std::endl;
  //if (ast->type) std::cerr << "\t\t" << *(ast->type) << std::endl;
}

void TypecheckPass::visit(UnaryOpExprAST* ast) {
  TypeAST* innerType = ast->parts[0]->type;
  const llvm::Type* opTy = innerType->getLLVMType();
  const std::string& op = ast->op;

  if (op == "-") {
    if (opTy == LLVMTypeFor("i1")) {
      std::cerr << "Typecheck error: unary '-' used on a boolean; use 'not' instead." << std::endl;
      return;
    }

    if (!(opTy->isIntOrIntVectorTy())) {
      std::cerr << "Typecheck error: operand to unary '-' had non-inty type " << *opTy << std::endl;
      return;
    }
  } else if (op == "not") {
    if (opTy != LLVMTypeFor("i1")) {
      std::cerr << "Typecheck error: operand to unary 'not' had non-bool type " << *opTy << std::endl;
      return;
    }
  }

  ast->type = innerType;
}

void TypecheckPass::visit(BinaryOpExprAST* ast) {
  TypeAST* Lty = ast->parts[ast->kLHS]->type;
  TypeAST* Rty = ast->parts[ast->kRHS]->type;
  const llvm::Type* TL = Lty->getLLVMType();

  const std::string& op = ast->op;

  if (! Lty->canConvertTo(Rty)) {
    std::cerr << "Error: binary expr " << op << " had differently typed sides!" << std::endl;
  } else if (!TL) {
    std::cerr << "Error: binary expr " << op << " failed to typecheck subexprs!" << std::endl;
  } else {
    if (op == "+" || op == "-" || op == "*" || op == "/") {
      if (!TL->isIntOrIntVectorTy()) {
        std::cerr << "Error: arith op '" << op << "' used with non-inty type " << *TL << std::endl;
        return;
      }
    }

    if (op == "bitand" || op == "bitor" || op == "bitxor" || op == "shl" || op == "lshr" || op == "ashr") {
      if (!TL->isIntOrIntVectorTy()) {
        std::cerr << "Error: bitwise op '" << op << "' used with non-inty type " << *TL << std::endl;
        return;
      }
    }

    if (op == "<" || op == "==" || op == "!=" || op == "<=") {
      ast->type = TypeAST::get(LLVMTypeFor("i1"));
    } else {
      ast->type = Lty;
    }
  }
}

bool areNamesDisjoint(const std::vector<VariableAST*>& vars) {
  std::map<std::string, bool> seen;
  for (int i = 0; i < vars.size(); ++i) {
    seen[vars[i]->name] = true;
  }
  return seen.size() == vars.size();
}

void TypecheckPass::visit(PrototypeAST* ast) {
  if (!areNamesDisjoint(ast->inArgs)) {
    std::cout << "Error: formal argument names for function "
              << ast->name << " are not disjoint!" << std::endl;
    return;
  }

  vector<TypeAST*> argTypes;
  for (int i = 0; i < ast->inArgs.size(); ++i) {
    assert(ast->inArgs[i] != NULL);

    if (ast->inArgs[i]->noFixedType()) {
      // Wait until type inference to resolve the arg's declared type.
      return;
    }
    ast->inArgs[i]->accept(this);
    TypeAST* ty =  ast->inArgs[i]->type;
    if (ty == NULL) {
      std::cerr << "Error: proto " << ast->name << " had "
        << "null type for arg '" << ast->inArgs[i]->name << "'" << std::endl;
      return;
    }

    std::cout << "\t\t" << ast->name << " arg " << i << " : " << *ty << std::endl;
    argTypes.push_back(ty);
  }

  if (!ast->resultTy && ast->tyExpr != NULL) {
    bool tyParMode = this->typeParsingMode; this->typeParsingMode = true;
    ast->tyExpr->accept(this);
    this->typeParsingMode = tyParMode;
    ast->resultTy = ast->tyExpr->type->getLLVMType();
  }

  if (!ast->resultTy) {
   std::cerr << "Error in typechecking PrototypeAST " << ast->name << ": null return type!" << std::endl;
  } else {
    ast->type = FnTypeAST::get(TypeAST::get(ast->resultTy), argTypes);
  }
}

void TypecheckPass::visit(FnAST* ast) {
  assert(ast->proto != NULL);
  ast->proto->accept(this); bool p = ast->proto->type != NULL;

  if (ast->body != NULL) {
    ast->body->accept(this);  bool b = ast->body->type  != NULL;

    if (p && b) {
      ast->type = ast->proto->type;
    }
  } else {
    // Probably looking at a function type expr. TODO trust but verify
    ast->type = ast->proto->type;
  }
}

void TypecheckPass::visit(ClosureTypeAST* ast) {
  ast->proto->accept(this);
  if (FnTypeAST* ft = tryExtractCallableType(ast->proto->type)) {
    ast->type = genericClosureTypeFor(ft);
    std::cout << "ClosureTypeAST typechecking converted " << *ft << " to " << *(ast->type) << std::endl;
  } else {
    std::cerr << "Error! Proto passed to ClosureType does not have function type!" << std::endl;
    std::cerr << *(ast->proto) << std::endl;
  }
}

void TypecheckPass::visit(ClosureAST* ast) {
  std::cout << "Type Checking closure AST node " << (*ast) << std::endl;
  if (ast->hasKnownEnvironment) {
    ast->fn->accept(this);
    visitChildren(ast);

    if (!ast->fn || !ast->fn->type) { return; }

    if (FnTypeAST* ft
          = tryExtractCallableType(ast->fn->type)) {
      ast->type = genericVersionOfClosureType(ft);
      if (ft && ast->type) {
        std::cout << "ClosureAST fnRef typechecking converted " << *ft << " to " << *(ast->type) << std::endl;
        //if (ast->fn && ast->fn->proto) { std::cout << "Just for kicks, fn has type " << *(ast->fn->proto) << std::endl; }
      }

    } else {
      std::cerr << "Error! 274 Function passed to closure does not have function type!" << std::endl;
      std::cerr << *(ast->fn) << std::endl;
    }
  } else {
    ast->fn->accept(this);
    if (FnTypeAST* ft = tryExtractCallableType(ast->fn->type)) {
      ast->type = genericClosureTypeFor(ft);
      std::cout << "ClosureTypeAST fn typechecking converted " << *ft << " to " << *(ast->type) << std::endl;
    } else {
      std::cerr << "Error! 282 Function passed to closure does not have function type!" << std::endl;
      std::cerr << *(ast->fn) << std::endl;
    }
  }
}

void TypecheckPass::visit(IfExprAST* ast) {
  assert(ast->testExpr != NULL);

  ast->testExpr->accept(this);
  const Type* ifType = ast->testExpr->type->getLLVMType();
  if (!ifType) {
    std::cerr << "if condition '" << *(ast->testExpr) << "' had null type!" << std::endl;
    return;
  }

  if (ifType != LLVMTypeFor("i1")) {
    std::cerr << "if condition '"      << *(ast->testExpr) << "' "
              << "had non-bool type "  << *ifType << std::endl;
    return;
  }

  ast->thenExpr->accept(this); TypeAST* thenType = ast->thenExpr->type;
  ast->elseExpr->accept(this); TypeAST* elseType = ast->elseExpr->type;

  if (thenType == NULL) {
    std::cerr << "IfExprAST had null type for 'then' expression" << std::endl;
    return;
  } else if (elseType == NULL) {
    std::cerr << "IfExprAST had null type for 'else' expression" << std::endl;
    return;
  } else if (thenType->getLLVMType() != elseType->getLLVMType()) {
    std::cerr << "IfExprAST had different (incompatible?) types for then/else exprs: "
    		<< "\n\t" << *thenType << " vs " << *elseType << std::endl;
    return;
  } else {
    ast->type = thenType;
  }
}

void TypecheckPass::visit(ForRangeExprAST* ast) {
  assert(ast->startExpr != NULL);

  // ast = for VAR in START to END by INCR do BODY

  // Check type of START
  ast->startExpr->accept(this);
  TypeAST* startType = ast->startExpr->type;
  if (!startType) {
    std::cerr << "for range start expression '" << *(ast->startExpr) << "' had null type!" << std::endl;
    return;
  } else if (startType->getLLVMType() != LLVMTypeFor("i32")) {
    std::cerr << "expected for range start expression to have type i32, but got type " << *startType << std::endl;
    return;
  }

  // Check that we can bind START to VAR
  ast->var->accept(this);
  if (!canAssignType(startType, ast->var->type)) {
	std::cerr << "Could not bind for range start expr to declared variable!" << std::endl;
	return;
  }

  // Check that END has same type as START
  assert(ast->endExpr != NULL);
  ast->endExpr->accept(this);
  TypeAST* endType = ast->endExpr->type;
  if (!endType) {
    std::cerr << "for range end expression '" << *(ast->endExpr) << "' had null type!" << std::endl;
    return;
  } else if (!hasEqualRepr(startType, endType)) {
	std::cerr << "for range start and end expressions had different types!" << std::endl;
	std::cerr << "for range start: " << str(startType) << std::endl;
	std::cerr << "for range end  : " << str(endType) << std::endl;
	return;
  }

  // Check that incrExpr, if it exists, has same type as START
  if (ast->incrExpr) {
	ast->incrExpr->accept(this);
	TypeAST* incrType = ast->incrExpr->type;
	if (!incrType) {
	  std::cerr << "for range incr expression '" << *(ast->incrExpr) << "' had null type!" << std::endl;
	  return;
	} else if (!hasEqualRepr(startType, incrType)) {
	  std::cerr << "for range start and incr expressions had different types!" << std::endl;
	  std::cerr << "for range start: " << str(startType) << std::endl;
	  std::cerr << "for range incr : " << str(incrType) << std::endl;
	    return;
	}
  }

  ast->bodyExpr->accept(this);
  TypeAST* bodyType = ast->bodyExpr->type;
  if (!bodyType) {
    std::cerr << "for range body expression '" << *(ast->bodyExpr) << "' had null type!" << std::endl;
    return;
  }

  ast->type = TypeAST::get(LLVMTypeFor("i32"));
}

int indexInParent(ExprAST* child, int startingIndex) {
  std::vector<ExprAST*>& parts = child->parent->parts;
  for (int i = startingIndex; i < parts.size(); ++i) {
    if (parts[i] == child) {
      return i;
    }
  }
  return -1;
}

void TypecheckPass::visit(NilExprAST* ast) {
  if (ast->type) return;

  // TODO this will eventually be superceded by real type inference
  if (ast->parent && ast->parent->parent) {
    if (ast->parent->parent->type) {
	  // If we have a type for the parent already, it's probably because
	  // it's a   new _type_ { ... nil ... }  -like expr.
      if (const llvm::StructType* tupleTy =
          llvm::dyn_cast<const llvm::StructType>(
		ast->parent->parent->type->getLLVMType())) {
        std::vector<ExprAST*>::iterator nilPos
                    = std::find(ast->parent->parts.begin(),
                                ast->parent->parts.end(),   ast);
        if (nilPos != ast->parent->parts.end()) {
          int nilOffset = std::distance(ast->parent->parts.begin(), nilPos);
          ast->type = TypeAST::get(tupleTy->getContainedType(nilOffset));
          std::cout << "\tmunging gave nil type " << *(ast->type) << std::endl;
        }
      }
    }

    // 'if (typed-expr ==/!= nil)'  --> nil should have type of other side
    if (IfExprAST* ifast = dynamic_cast<IfExprAST*>(ast->parent->parent)) {
      if (BinaryOpExprAST* cmpast = dynamic_cast<BinaryOpExprAST*>(ast->parent)) {
        if (cmpast->parts[0]->type) {
          ast->type = cmpast->parts[0]->type;
        } else if (cmpast->parts[1]->type) {
          ast->type = cmpast->parts[1]->type;
        }
      }
    }

    // callee(... nil ...)
    if (CallAST* callast = dynamic_cast<CallAST*>(ast->parent)) {
      // find the arg position of our nil
      ExprAST* callee = callast->parts[0];
      const llvm::Type* loweredType = callee->type->getLLVMType();

      // First, try converting closures to their underlying fn type
      if (isValidClosureType(loweredType)) {
        FnTypeAST* f = originalFunctionTypeForClosureStructType(callee->type);
        loweredType = f->getLLVMType();
      }

      if (const llvm::FunctionType* fnty =
	  llvm::dyn_cast_or_null<const llvm::FunctionType>(loweredType)) {
        // callast.parts[0] is callee; args start at 1
        int i = indexInParent(ast, 1);
        if (i >= 0) {
          // TODO should this stay in TypeAST?
          ast->type = TypeAST::get(fnty->getParamType(i - 1));
        }
      } else {
        std::cout << "\t\tCALLEE HAS TYPE " << *(callee->type) << std::endl;
      }
    }

    if (TupleExprAST* tupleast = dynamic_cast<TupleExprAST*>(ast->parent->parent)) {
      if (!tupleast->typeName.empty()) {
        TypeAST* ty = typeScope.lookup(tupleast->typeName, "");
        if (TupleTypeAST* tuplety = dynamic_cast<TupleTypeAST*>(ty)) {
          int i = indexInParent(ast, 0);
          if (i >= 0) {
            TypeAST* targetType = tuplety->getContainedType(i);
            ast->type = RefTypeAST::getNullableVersionOf(targetType);
          }
        } else {
          std::cerr << "Warning: expected type " << tupleast->typeName
              << " to have TupleTypeAST; has type " << str(ty) << std::endl;
        }
      }
    }
  }

  if (!ast->type) {
	std::cerr << "TODO: munge around to extract expected (pointer) type of nil exprs" << std::endl;
	std::cout << "nil parent: " << *(ast->parent) << std::endl;
	std::cout << "nil parent parent: " << *(ast->parent->parent) << std::endl;
	std::cout << "nil parent parent ty: " << ast->parent->parent->type << std::endl;

	ast->type = RefTypeAST::get(TypeAST::get(LLVMTypeFor("i8")), true);
  } else {
    // make sure it's a nullable type, since this is nil...
    if (RefTypeAST* ref = dynamic_cast<RefTypeAST*>(ast->type)) {
      if (!ref->isNullable()) {
        ast->type = RefTypeAST::getNullableVersionOf(ast->type); 
      }
    }
    std::cout << "nil given type: " << str(ast->type) << std::endl;
  }
}

bool exprBindsName(ExprAST* ast, const std::string& name) {
  // TODO test for-range exprs
  if (FnAST* fn = dynamic_cast<FnAST*>(ast)) {
    PrototypeAST* proto = fn->proto;
    for (int i = 0; i < proto->inArgs.size(); ++i) {
      if (proto->inArgs[i]->name == name) {
        return true;
      }
    }
    return false;
  }

  if (ClosureAST* clo = dynamic_cast<ClosureAST*>(ast)) {
    std::cout << "TODO: does " << str(clo)
              << " bind variable " << name << "???" << std::endl;
  }
}

enum NullTestStatus {
  eNoTest,
  eThenBranch,
  eElseBranch
};

bool isNil(ExprAST* ast) {
  if (NilExprAST* enil = dynamic_cast<NilExprAST*>(ast)) {
    return true;
  } else {
    return false;
  }
}

// var == nil, nil == var ==> elsebranch
// var != nil, nil != var ==> thenbranch
// else: notest
NullTestStatus examineForNullTest(ExprAST* test, VariableAST* var) {
  std::cout << "TEsT: " << str(test) << std::endl;
  if (BinaryOpExprAST* binopExpr = dynamic_cast<BinaryOpExprAST*>(test)) {
    ExprAST* lhs = binopExpr->parts[0];
    ExprAST* rhs = binopExpr->parts[1];
    bool lhsnil = isNil(lhs);
    bool rhsnil = isNil(rhs);
    bool lhsvar = (lhs == var);
    bool rhsvar = (rhs == var);

    if (lhsnil && rhsvar || lhsvar && rhsnil) {
      return (binopExpr->op == "==") ? eElseBranch : eThenBranch;
    }
  }
  return eNoTest;
}

// A nullable pointer is okay to deref if it has been tested
// for nullness, successfully.
// There should exist some parent, P, with parent(P) = P_if,
// such that P_if is an IfExpr testing ast for nullity
// and P is the appropriate branch of P_if (such that ast
// will be non-nil).
// Note that the search terminates at the closest lexical
// binding of ast.
bool isOkayToDeref(VariableAST* ast, ExprAST* parent) {
  std::cout << "\t\tAST = " << str(ast) << std::endl;
  while (parent) {
    if (exprBindsName(parent, ast->name)) {
      std::cout << "Found the closest lexical binding for " << ast->name
		<< ", so ending search (not okay to deref)" << std::endl;
      break;
    }
    ExprAST* pp = parent->parent;
    if (!pp) break;
    if (IfExprAST* Pif = dynamic_cast<IfExprAST*>(pp)) {
      NullTestStatus status = examineForNullTest(Pif->testExpr, ast);
      if (status == eElseBranch && Pif->elseExpr == parent) return true;
      if (status == eThenBranch && Pif->thenExpr == parent) return true;
    }
    parent = parent->parent;
  }
  return false;
}

// In order for copying GC to be able to move GC roots,
// the root must be stored on the stack; thus, new T is implemented
// so that it evaluates to a T** (a stack slot containing a T*)
// instead of a simple T*, which would not be modifiable by the GC.
void TypecheckPass::visit(RefExprAST* ast) {
  assert(ast->parts[0]->type && "Need arg to typecheck ref!");
  if (ast->parts[0]->type) {
    ast->type = RefTypeAST::get(
                      ast->parts[0]->type,
                      ast->isNullable);
  } else {
    ast->type = NULL;
  }

  std::cout << "refexpr (" << ast->isNullable << ") = " << str(ast->type) << std::endl;
}

void TypecheckPass::visit(DerefExprAST* ast) {
  assert(ast->parts[0]->type && "Need arg to typecheck deref!");

  TypeAST* derefType = ast->parts[0]->type;
  if (RefTypeAST* ptrTy = dynamic_cast<RefTypeAST*>(derefType)) {
    ast->type = ptrTy->getElementType();

    if (ptrTy->isNullable()) {
      if (VariableAST* var = dynamic_cast<VariableAST*>(ast->parts[0])) {
	if (!isOkayToDeref(var, ast->parent)) {
	  ast->type = NULL;
	}
      } else {
        // If it's not a variable, we'll suppose (for the sake of
        //  simplification) that it hasn't been tested for nullity.
        ast->type = NULL;
      }
    }
  } else {
    std::cerr << "Deref() called on a non-pointer type " << *derefType << "!\n";
    std::cerr << "base: " << *(ast->parts[0]) << std::endl;
    ast->type = NULL;
  }
}

void TypecheckPass::visit(AssignExprAST* ast) {
  TypeAST* lhsTy = ast->parts[0]->type;
  TypeAST* rhsTy = ast->parts[1]->type;

  if (RefTypeAST* plhsTy = dynamic_cast<RefTypeAST*>(lhsTy)) {
    lhsTy = plhsTy->getElementType();
    if (rhsTy->canConvertTo(lhsTy)) {
      ast->type = TypeAST::get(LLVMTypeFor("i32"));
    } else {
      std::cerr << "Types in assignment are not copy compatible!" << std::endl;
      std::cerr << "\tLHS (deref'd): " << *(lhsTy) << std::endl;
      std::cerr << "\tRHS          : " << *(rhsTy) << std::endl;
      ast->type = NULL;
    }
  } else {
    std::cerr << "Attempted assignment to a non-pointer (internally) type " << *lhsTy << "!\n";
    std::cerr << "AST dump: " << *(ast) << std::endl;
    ast->type = NULL;
  }
}

// Returns aggregate and vector types directly, and returns the underlying
// aggregate type for pointer-to-aggregate. Returns NULL in other cases.
const llvm::CompositeType* getIndexableType(const llvm::Type* ty) {
  const llvm::Type* baseType = ty;
  //std::cout << "getIndexableType: " << *ty << std::endl;
  if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    ty = pty->getElementType();
  }

  if (ty->isAggregateType() || llvm::isa<llvm::VectorType>(ty)) {
    return llvm::dyn_cast<llvm::CompositeType>(ty);
  } else {
    std::cerr << "Error: Cannot index into non-aggregate type " << *baseType << std::endl;
    return NULL;
  }
}

void TypecheckPass::visit(SubscriptAST* ast) {
  if (!ast->parts[1]) {
    std::cerr << "Error: " << *(ast) << " had null index" << std::endl;
    return;
  }

  ExprAST* index = ast->parts[1];
  IntAST* idx = dynamic_cast<IntAST*>(index);
  if (!idx) {
    std::cerr << "Error: SubscriptAST needs constant int (IntAST) index; got '"
              << *(index) << "'";
    if (index->type) {
      std::cerr << " of type " << *(index->type);
    }
    std::cerr << std::endl;
    return;
  }

  TypeAST* baseType = ast->parts[0]->type;
  if (!baseType) {
    std::cerr << "Error: Cannot index into object of null type " << std::endl;
    return;
  }

  const llvm::Type* loweredBaseType = baseType->getLLVMType();
  const llvm::CompositeType* compositeTy = getIndexableType(loweredBaseType);
  if (compositeTy == NULL) {
    std::cerr << "Error: attempt to index into a non-composite type " << *baseType << std::endl;
    return;
  }

  //std::cout << "Indexing " << *baseType << " as composite " << *compositeTy << std::endl;

  // Check to see that the given index is valid for this type
  ConstantInt* cidx = llvm::dyn_cast<ConstantInt>(idx->getConstantValue());
  const APInt& vidx = cidx->getValue();

  if (!vidx.isSignedIntN(64)) { // an exabyte of memory should be enough for anyone!
    llvm::errs() << "Error: Indices must fit in 64 bits; tried to index with '" << *cidx << "'" << "\n";
    return;
  }

  if (!compositeTy->indexValid(cidx) || vidx.isNegative()) {
    llvm::errs() << "Error: attempt to index composite with invalid index '" << *cidx << "'" << "\n";
    return;
  }

  // LLVM doesn't do bounds checking for arrays or vectors, but we do!
  uint64_t numElements = -1;
  if (const llvm::ArrayType* ty = llvm::dyn_cast<llvm::ArrayType>(loweredBaseType)) {
    numElements = ty->getNumElements();
  }

  if (const llvm::VectorType* ty = llvm::dyn_cast<llvm::VectorType>(loweredBaseType)) {
    numElements = ty->getNumElements();
  }

  if (numElements >= 0) {
    uint64_t idx_u64 = vidx.getZExtValue();
    if (idx_u64 >= numElements) {
      llvm::errs() << "Error: attempt to index array[" << numElements << "]"
                   << " with invalid index '" << idx_u64 << "'" << "\n";
      return;
    }
  }

  //llvm::errs() << "Indexing composite with index " << *cidx << "; neg? " << vidx.isNegative() << "\n";

  // TODO need to avoid losing typeinfo here
  ast->type = TypeAST::get(compositeTy->getTypeAtIndex(cidx));

  if (this->inAssignLHS) {
    ast->type = TypeAST::get(llvm::PointerType::getUnqual(ast->type->getLLVMType()));
  }
}

void TypecheckPass::visit(SeqAST* ast) {
  bool success = true;
  for (int i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      if (!ast->parts[i]->type) { success = false; }
    } else {
      std::cerr << "Null expr in SeqAST" << std::endl;
      return;
    }
  }

  if (!success || ast->parts.empty()) { return; }

  ast->type = ast->parts.back()->type;
}

const FunctionType* getFunctionTypeFromClosureStructType(const Type* ty) {
  if (const llvm::StructType* sty = llvm::dyn_cast<llvm::StructType>(ty)) {
    if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(sty->getContainedType(0))) {
      return llvm::dyn_cast<llvm::FunctionType>(pty->getElementType());
    }
  }
  std::cerr << "ERROR: failed to get function type from closure struct type: " << *ty << std::endl;
  exit(1);
  return NULL;
}

void TypecheckPass::visit(CallAST* ast) {
  ExprAST* base = ast->parts[0];
  if (!base) {
    std::cerr << "Error: CallAST has null base!" << std::endl;
    return;
  }

  base->accept(this);
  TypeAST* baseType = base->type;
  if (baseType == NULL) {
    std::cerr << "Error: CallAST base expr had null type:\n\t" << *(base) << std::endl;
    return;
  }

  // HACK HACK HACK - give print_ref special polymorphic type (with hardcoded ret ty)
  if (isPrintRef(base)) {
    if (ast->parts.size() < 2) {
      std::cerr << "print_ref() must be given an arg!" << std::endl;
      return;
    }
    ExprAST* arg = ast->parts[1];
    arg->accept(this);
    if (!arg->type) {
      std::cerr << "print_ref() given arg of no discernable type!" << std::endl;
    } else if (!arg->type->getLLVMType()->isPointerTy()) {
      std::cerr << "print_ref() given arg of non-pointer type! " << *(arg->type) << std::endl;
    } else {
      ast->type = TypeAST::get(LLVMTypeFor("i32"));
    }
    return;
  }

  FnTypeAST* baseFT = tryExtractCallableType(baseType);
  if (baseFT == NULL) {
    baseFT = originalFunctionTypeForClosureStructType(baseType);
  }

  if (baseFT == NULL) {
    std::cerr << "Error: CallAST base expr had non-callable type " << *baseType << std::endl;
    return;
  }

  vector<TypeAST*> actualTypes;
  vector<ExprAST*> literalArgs; // any args not from unpack exprs, temp hack!
  for (int i = 1; i < ast->parts.size(); ++i) {
    ExprAST* arg = ast->parts[i];
    if (!arg) {
      std::cerr << "Null arg " << i << " for CallAST" << std::endl;
      return;
    }

    arg->accept(this);
    TypeAST* argTy = arg->type;
    if (!argTy) {
      std::cerr << "Error: CallAST typecheck: arg " << i << " (" << *(arg) << ") had null type" << std::endl;
      return;
    }

    // TODO: add separate prepass to explicitly unpack UnpackExprASTs
    if (UnpackExprAST* u = dynamic_cast<UnpackExprAST*>(arg)) {
      if (const llvm::StructType* st = llvm::dyn_cast<llvm::StructType>(argTy->getLLVMType())) {
        for (int j = 0; j < st->getNumElements(); ++j) {
          actualTypes.push_back(TypeAST::get(st->getElementType(j)));
          literalArgs.push_back(NULL);
        }
      } else {
        std::cerr << "Error: call expression found UnpackExpr with non-struct type " << *argTy << std::endl;
      }
    } else {
      actualTypes.push_back(argTy);
      literalArgs.push_back(arg);
    }
  }

  int numParams = baseFT->getNumParams();
  if (numParams != actualTypes.size()) {
    std::cerr << "Error: arity mismatch; " << actualTypes.size() << " args provided"
      << " for function " << *(base) << std::endl <<  " of type " << *(baseFT) <<  " taking " << numParams << " args." << std::endl;
    return;
  }

  bool success = true;
  for (int i = 0; i < numParams; ++i) {
    TypeAST* formalType = baseFT->getParamType(i);
    TypeAST* actualType = actualTypes[i];

    if (const FunctionType* fnty = llvm::dyn_cast<const FunctionType>(actualType->getLLVMType())) {
      // If we try to use  fa: i32 () in place of ff: void ()*,
      // temporarily give the function fa the type of ff.
      if (isPointerToCompatibleFnTy(formalType->getLLVMType(), fnty)) {
        actualType = formalType;
      } else {
        // Temporarily view a function type as its associated specific closure type,
        // since the formal arguments will have undergone the same conversion.
        actualType = genericClosureTypeFor(dynamic_cast<FnTypeAST*>(actualType));
        std::cout << "TYPECHECK CallAST converting " << *fnty << " to " << *actualType << std::endl;
        std::cout << "\t for formal type:\t" << *formalType << std::endl;
        std::cout << "\t base :: " << *base << std::endl;
      }
    } else if (const llvm::StructType* sty = llvm::dyn_cast<llvm::StructType>(actualType->getLLVMType())) {
      if (isValidClosureType(sty)) {
        FnTypeAST* fnty = originalFunctionTypeForClosureStructType(actualType);
        if (isPointerToCompatibleFnTy(formalType->getLLVMType(),
             llvm::cast<FunctionType>(fnty->getLLVMType()))) {
          // We have a closure and will convert it to a bare
          // trampoline function pointer at codegen time.
          actualType = formalType;

          if (ExprAST* arg = literalArgs[i]) {
             if (ClosureAST* clo = dynamic_cast<ClosureAST*>(arg)) {
               clo->isTrampolineVersion = true;
             } else {
               std::cerr << "Error! LLVM requires literal closure definitions"
                         << " be given at trampoline creation sites!\n";
               return;
             }
          } else {
            std::cerr << "Error! LLVM requires literal closure definitions"
                      << " be given at trampoline creation sites! Can't use an unpacked tuple!\n";
            return;
          }
        }
      }
    }

    if (!actualType->canConvertTo(formalType)) {
      success = false;
      std::cerr << "Type mismatch between actual and formal arg " << i << std::endl;
      std::cerr << "\tformal: " << *formalType << "; actual: " << *actualType << std::endl;
    }
  }

  if (!success) {
    std::cerr << "Error in typechecking call of"
              << "\n\t" << *(ast->parts[0]) << "\tof type\t" << *(baseFT) << "\t with args ";
    for (int i = 1; i < ast->parts.size(); ++i) {
      std::cerr << "\n\t" << i << ":\t";
      if (ExprAST* arg = ast->parts[i]) {
        std::cerr << *arg << " : " << str(arg->type);
      } else {
        std::cerr << "<NULL arg>" << std::endl;
      }
    }
  }

  if (success) {
    ast->type = baseFT->getReturnType();
  }
}

/// For now, as a special case, simd-vector and array will interpret { 4;i32 }
/// as meaning the same thing as { i32 ; i32 ; i32 ; i32 }
int extractNumElementsAndElementType(int maxSize, ExprAST* ast, const Type*& elementType) {
  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  IntAST* first = dynamic_cast<IntAST*>(body->parts[0]);
  VariableAST* var = dynamic_cast<VariableAST*>(body->parts[1]);
  if (first && var) {
    APInt v = first->getAPInt();
    unsigned int n = v.getZExtValue();
    // Sanity check on # elements; nobody? wants a single billion-element vector...
    if (n <= maxSize) {
      elementType = var->type->getLLVMType();
      return n;
    } else {
      std::cerr << "Concise simd/array declaration too big! : " << *ast << std::endl;
    }
  }
  return 0;
}

void TypecheckPass::visit(ArrayExprAST* ast) {
  bool success = true;
  std::map<const Type*, bool> fieldTypes;

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (!body) {
    std::cerr << "Typecheck of array expr failed because ast.parts[0] = " << ast->parts[0] << " was not a Seq!" << std::endl;
    return;
  }

  int numElements = body->parts.size();
  const Type* elementType = NULL;

  if (numElements == 2) {
    numElements = extractNumElementsAndElementType(256, ast, elementType);
    if (numElements != 0) {
      // Don't try to interpret the size + type as initializers!
      body->parts.clear();
    } else {
      numElements = 2;
    }
  }

  if (!elementType) {
    for (int i = 0; i < numElements; ++i) {
      const Type* ty =  body->parts[i]->type->getLLVMType();
      if (!ty) {
        std::cerr << "Array expr had null constituent type for subexpr " << i << std::endl;
        success = false;
        break;
      }
      fieldTypes[ty] = true;
      elementType = ty;
    }

    // TODO This should probably be relaxed eventually; for example,
    // an array of "small" and "large" int literals should silently be accepted
    // as an array of "large" ints.
    if (success && fieldTypes.size() > 1) {
      std::cerr << "Array expression had multiple types! Found:" << std::endl;
      std::map<const Type*, bool>::const_iterator it;;
      for (it = fieldTypes.begin(); it != fieldTypes.end(); ++it) {
        std::cerr << "\t" << *((*it).first) << std::endl;
      }
      success = false;
    }
  }

  if (!elementType) {
    std::cerr << "Error: Array had no discernable element type?!?" << std::endl;
    return;
  }


  if (success) {
    ast->type = TypeAST::get(llvm::ArrayType::get(elementType, numElements));
  }
}

bool isPrimitiveNumericType(const Type* ty) {
  return ty->isFloatingPointTy() || ty->isIntegerTy();
}

// TODO this is a near-exact duplicate of ArrayExprAST* case...
// but unlike an array, simd vectors are limited to numeric base types
void TypecheckPass::visit(SimdVectorAST* ast) {
  bool success = true;
  std::map<const Type*, bool> fieldTypes;

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (!body) {
    std::cerr << "Typecheck of simd-vector expr failed because ast.parts[0] = " << ast->parts[0] << " was not a Seq!" << std::endl;
    return;
  }

  int numElements = body->parts.size();
  const Type* elementType = NULL;

  if (numElements == 2) {
    numElements = extractNumElementsAndElementType(256, ast, elementType);
  }

  // No special case; iterate through and collect all the types
  if (!elementType) {
    for (int i = 0; i < numElements; ++i) {
      const Type* ty =  body->parts[i]->type->getLLVMType();
      if (!ty) {
        std::cerr << "simd-vector expr had null constituent type for subexpr " << i << std::endl;
        success = false;
        break;
      }
      fieldTypes[ty] = true;
      elementType = ty;
    }

    // TODO This should probably be relaxed eventually; for example,
    // a simd-vector of "small" and "large" int literals should silently be accepted
    // as a simd-vector of "large" ints.
    if (success && fieldTypes.size() != 1) {
      std::cerr << "simd-vector expression had multiple types! Found:" << std::endl;
      std::map<const Type*, bool>::const_iterator it;;
      for (it = fieldTypes.begin(); it != fieldTypes.end(); ++it) {
        std::cerr << "\t" << *((*it).first) << std::endl;
      }
      success = false;
    }

    if (success && !isPrimitiveNumericType(elementType)) {
      std::cerr << "simd-vector expression must be composed of primitive numeric types!" << std::endl;
      success = false;
    }
  }

  if (!isSmallPowerOfTwo(numElements)) {
    std::cerr << "simd-vector constructor needs a small"
              << " power of two of elements; got " << numElements << std::endl;
    success = false;
  }

  if (success) {
    ast->type = TypeAST::get(llvm::VectorType::get(elementType, numElements));
  }
}

void TypecheckPass::visit(TupleExprAST* ast) {
  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (!body) {
    std::cerr << "Error: typechecking tuple failed; body is not a Seq!" << std::endl;
    return;
  }

  TupleTypeAST* expectedTupleType = NULL;
  if (!ast->typeName.empty()) {
    expectedTupleType = dynamic_cast<TupleTypeAST*>(typeScope.lookup(ast->typeName, ""));
  }

  if (expectedTupleType) {
    int expectedSize = expectedTupleType->getNumContainedTypes();
    if (expectedSize != body->parts.size()) {
      std::cerr << "Error: mismatch between size of tuple type (" << expectedSize << ")"
          << " and number of expressions in tuple (" << body->parts.size() << ")" << std::endl;
      return;
    }
  }

  bool success = true;
  std::vector<TypeAST*> tupleFieldTypes;
  for (int i = 0; i < body->parts.size(); ++i) {
    ExprAST* expr = body->parts[i];
    if (!expr) {
      std::cerr << "Tuple expr had null component " << i << "!" << std::endl;
      break;
    }
    TypeAST* ty = expr->type;
    if (!ty) {
      std::cerr << "Tuple expr had null constituent type for subexpr " << i << std::endl;
      success = false;
      break;
    }

    if (expectedTupleType) {
      TypeAST* expectedType = expectedTupleType->getContainedType(i);
      std::cerr << ast->typeName << " :: " << str(expectedTupleType) << " " << i
          << "; low: " << str(expectedTupleType->getLLVMType())
          << "; ty = " << str(ty) << "; exp " << expectedType << std::endl;
      if (!ty->canConvertTo(expectedType)) {
        std::cerr << "Typecheck error in constructing tuple,"
                  << " type mismatch at parameter " << i << ": "
                  << str(ty) << " vs expected type " << str(expectedType) << std::endl;
        success = false;
        break;
      }
    }

    tupleFieldTypes.push_back(ty);
  }

  if (success) {
    ast->type = TupleTypeAST::get(tupleFieldTypes);
  }

  fail:
  return;
}


void TypecheckPass::visit(UnpackExprAST* ast) {
  const llvm::Type* unpackeeType = 
     ast->parts[0]->type->getLLVMType();
  if (!llvm::isa<llvm::StructType>(unpackeeType)) {
    std::cerr << "Cannot unpack non-struct expression:\n\t" << *(ast->parts[0])
              << "of type\n\t" << *(unpackeeType) << std::endl;
  } else {
    // This is really just a valid non-null pointer; since an unpack
    // "expression" is syntactic sugar for a complex expression that
    // generates multiple values, it doesn't have a single well-defined type...
    // But this is the closest thing, and is useful for type checking calls.
    ast->type = ast->parts[0]->type;
  }
}

void TypecheckPass::visit(BuiltinCompilesExprAST* ast) {
  if (ast->parts[0]) {
    ast->parts[0]->accept(this);
    ast->status = (ast->parts[0]->type != NULL) ? ast->kWouldCompile : ast->kWouldNotCompile;
  } else {
    ast->status = ast->kWouldNotCompile;
  }
  ast->type = TypeAST::get(LLVMTypeFor("i1"));
}

