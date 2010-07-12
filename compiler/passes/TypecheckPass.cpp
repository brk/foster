// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "passes/TypecheckPass.h"
#include "parse/FosterAST.h"
#include "FosterUtils.h"

using foster::EDiag;
using foster::show;

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
  return NULL;
}

void TypecheckPass::visit(IntAST* ast) {
  // Make sure the base is a reasonable one
  if (!(ast->Base == 2  || ast->Base == 8
     || ast->Base == 10 || ast->Base == 16)) {
    EDiag() << "int base must be 2, 8, 10, or 16, but was " << ast->Base << show(ast);
    return;
  }

  // Make sure the literal only contains
  // valid digits for the chosen base.
  const char* digits = "0123456789abcdef";
  for (size_t i = 0; i < ast->Clean.size(); ++i) {
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
  }

  ast->type = TypeAST::get(LLVMintTypeForNBits(activeBits));
}

void TypecheckPass::visit(VariableAST* ast) {
  if (ast->type) { return; }
  
  EDiag() << "variable " << ast->name << " has no type!" << show(ast);
}

void TypecheckPass::visit(UnaryOpExprAST* ast) {
  TypeAST* innerType = ast->parts[0]->type;
  const llvm::Type* opTy = innerType->getLLVMType();
  const std::string& op = ast->op;

  if (op == "-") {
    if (opTy == LLVMTypeFor("i1")) {
      EDiag() << "unary '-' used on a boolean; use 'not' instead" << show(ast);
      return;
    }

    if (!(opTy->isIntOrIntVectorTy())) {
      EDiag() << "operand to unary '-' had non-inty type " << str(opTy) << show(ast);
      return;
    }
  } else if (op == "not") {
    if (opTy != LLVMTypeFor("i1")) {
      EDiag() << "operand to unary 'not had non-bool type " << str(opTy) << show(ast);
      return;
    }
  }

  ast->type = innerType;
}

bool isBitwiseOp(const std::string& op) {
  return op == "bitand" || op == "bitor" || op == "bitxor"
      || op == "shl" || op == "lshr" || op == "ashr";
}

void TypecheckPass::visit(BinaryOpExprAST* ast) {
  TypeAST* Lty = ast->parts[ast->kLHS]->type;
  TypeAST* Rty = ast->parts[ast->kRHS]->type;
  const llvm::Type* TL = Lty->getLLVMType();

  const std::string& op = ast->op;

  if (! Lty->canConvertTo(Rty)) {
    // TODO handle conversions more systematically, and symmetrically
    EDiag() << "binary op '" << op << "' had differently typed sides"
            << show(ast);
  } else if (!TL) {
    EDiag() << "binary op '" << op << "' failed to typecheck subexprs"
            << show(ast);
  } else {
    if (op == "+" || op == "-" || op == "*" || op == "/") {
      if (!TL->isIntOrIntVectorTy()) {
        EDiag() << "opr '" << op << "' used with non-inty type " << str(TL)
                << show (ast);
        return;
      }
    }

    if (isBitwiseOp(op)) {
      if (!TL->isIntOrIntVectorTy()) {
        EDiag() << "bitwise op '" << op << "' used with non-inty type "
                << str(TL) << show(ast);
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
  for (size_t i = 0; i < vars.size(); ++i) {
    seen[vars[i]->name] = true;
  }
  return seen.size() == vars.size();
}

void TypecheckPass::visit(PrototypeAST* ast) {
  if (!areNamesDisjoint(ast->inArgs)) {
    EDiag() << "formal argument names for function "
              << ast->name << " are not disjoint" << show(ast);
    return;
  }

  vector<TypeAST*> argTypes;
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    ASSERT(ast->inArgs[i] != NULL);

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

    argTypes.push_back(ty);
  }

  if (!ast->resultTy && ast->type != NULL) {
    EDiag() << "TYPE BU NO RESULT TYPE FOR PROTO" << show(ast);
  }

  if (!ast->resultTy) {
    EDiag() << "NULL return type for PrototypeAST " << ast->name << show(ast);
  } else {
    ast->type = FnTypeAST::get(ast->resultTy, argTypes);
  }
}

void TypecheckPass::visit(FnAST* ast) {
  ASSERT(ast->proto != NULL);
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
        EDiag() << "ClosureAST fnRef typechecking converted "
                 << str(ft) << " to " << str(ast->type) << show(ast);
        if (false && ast->fn && ast->fn->proto) {
          std::cout << "Just for kicks, fn has type "
                    << *(ast->fn->proto) << std::endl;
        }
      }

    } else {
      EDiag() << "Error! 274 Function passed to closure"
              << " does not have function type!" << show(ast);
    }
  } else {
    ast->fn->accept(this);
    if (FnTypeAST* ft = tryExtractCallableType(ast->fn->type)) {
      ast->type = genericClosureTypeFor(ft);
      EDiag() << "ClosureTypeAST fn typechecking converted "
              << str(ft) << " to " << str(ast->type) << show(ast);
    } else {
      EDiag() << "Error! 282 Function passed to closure"
              << "does not have function type!" << show(ast);
    }
  }
}

void TypecheckPass::visit(IfExprAST* ast) {
  ASSERT(ast->testExpr != NULL);

  ast->testExpr->accept(this);
  const Type* ifType = ast->testExpr->type->getLLVMType();
  if (!ifType) {
    EDiag() << "if condition had null type" << show(ast->testExpr);
    return;
  }

  if (ifType != LLVMTypeFor("i1")) {
    EDiag() << "if condition had non-bool type " << str(ifType)
            << show(ast->testExpr);
    return;
  }

  ast->thenExpr->accept(this); TypeAST* thenType = ast->thenExpr->type;
  ast->elseExpr->accept(this); TypeAST* elseType = ast->elseExpr->type;

  if (thenType == NULL) {
    EDiag() << "null type for 'then' branch of if expression"
            << show(ast->thenExpr);
    return;
  } else if (elseType == NULL) {
    EDiag() << "null type for 'else' branch of if expression"
            << show(ast->elseExpr);
    return;
  } else if (thenType->getLLVMType() != elseType->getLLVMType()) {
    EDiag() << "if expression had different types for then/else branches: "
            << "then: " << str(thenType->getLLVMType())
            << "vs else: " << str(elseType->getLLVMType())
            << show(ast);
    return;
  } else {
    ast->type = thenType;
  }
}

void TypecheckPass::visit(ForRangeExprAST* ast) {
  ASSERT(ast->startExpr != NULL);

  // ast = for VAR in START to END by INCR do BODY

  // Check type of START
  ast->startExpr->accept(this);
  TypeAST* startType = ast->startExpr->type;
  if (!startType) {
    EDiag() << "for range start expression had null type"
            << show(ast->startExpr);
    return;
  } else if (startType->getLLVMType() != LLVMTypeFor("i32")) {
    EDiag() << "expected for range start expression to have type i32,"
            << " but got type " << str(startType) << show(ast->startExpr);
    return;
  }

  // Check that we can bind START to VAR
  ast->var->accept(this);
  if (!canAssignType(startType, ast->var->type)) {
	EDiag() << "could not bind for range start expr to declared variable!"
            << show(ast);
	return;
  }

  // Check that END has same type as START
  ASSERT(ast->endExpr != NULL);
  ast->endExpr->accept(this);
  TypeAST* endType = ast->endExpr->type;
  if (!endType) {
    EDiag() << "for range end expression had null type"
            << show(ast->endExpr);
    return;
  } else if (!hasEqualRepr(startType, endType)) {
	EDiag() << "for range start and end expressions had different types\n"
	        << "for range start: " << str(startType) << "\n"
	        << "for range end  : " << str(endType) << show(ast->endExpr);
	return;
  }

  // Check that incrExpr, if it exists, has same type as START
  if (ast->incrExpr) {
	ast->incrExpr->accept(this);
	TypeAST* incrType = ast->incrExpr->type;
	if (!incrType) {
      EDiag() << "for range incr expression had null type"
              << show(ast->endExpr);
	  return;
	} else if (!hasEqualRepr(startType, incrType)) {
      EDiag() << "for range start and incr expressions had different types\n"
              << "for range start: " << str(startType) << "\n"
              << "for range incr : " << str(incrType) << show(ast->incrExpr);
	    return;
	}
  }

  ast->bodyExpr->accept(this);
  TypeAST* bodyType = ast->bodyExpr->type;
  if (!bodyType) {
    EDiag() << "for range body expression had null type" << show(ast->bodyExpr);
    return;
  }

  ast->type = TypeAST::get(LLVMTypeFor("i32"));
}

int indexInParent(ExprAST* child, int startingIndex) {
  std::vector<ExprAST*>& parts = child->parent->parts;
  for (size_t i = startingIndex; i < parts.size(); ++i) {
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
    if (dynamic_cast<IfExprAST*>(ast->parent->parent)) {
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
    ////std::cout << "nil given type: " << str(ast->type) << std::endl;
  }
}

bool exprBindsName(ExprAST* ast, const std::string& name) {
  // TODO test for-range exprs
  if (FnAST* fn = dynamic_cast<FnAST*>(ast)) {
    PrototypeAST* proto = fn->proto;
    for (size_t i = 0; i < proto->inArgs.size(); ++i) {
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
  return false;
}

enum NullTestStatus {
  eNoTest,
  eThenBranch,
  eElseBranch
};

bool isNil(ExprAST* ast) {
  if (dynamic_cast<NilExprAST*>(ast)) {
    return true;
  } else {
    return false;
  }
}

// var == nil, nil == var ==> elsebranch
// var != nil, nil != var ==> thenbranch
// else: notest
NullTestStatus examineForNullTest(ExprAST* test, VariableAST* var) {
  ////std::cout << "TEsT: " << str(test) << std::endl;
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
  if (ast->parts[0] && ast->parts[0]->type) {
    ast->type = RefTypeAST::get(
                      ast->parts[0]->type,
                      ast->isNullable);
  } else {
    ast->type = NULL;
  }
}

void TypecheckPass::visit(DerefExprAST* ast) {
  ASSERT(ast->parts[0]->type) << "Need arg to typecheck deref!";

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
      EDiag() << "types in assignment not copy-compatible"
              << "\n\tLHS (deref'd): " << str(lhsTy)
              << "\n\tRHS          : " << str(rhsTy)
              << show(ast);
      ast->type = NULL;
    }
  } else {
    EDiag() << "attempted to assign to a non-pointer type " << str(lhsTy)
            << show(ast);
    ast->type = NULL;
  }
}

// Returns aggregate and vector types directly, and returns the underlying
// aggregate type for pointer-to-aggregate. Returns NULL in other cases.
const llvm::CompositeType* tryGetIndexableType(const llvm::Type* ty) {
  if (const llvm::PointerType* pty = llvm::dyn_cast<llvm::PointerType>(ty)) {
    ty = pty->getElementType();
  }

  if (ty->isAggregateType() || llvm::isa<llvm::VectorType>(ty)) {
    return llvm::dyn_cast<llvm::CompositeType>(ty);
  } else {
    return NULL;
  }
}

void TypecheckPass::visit(SubscriptAST* ast) {
  if (!ast->parts[1]) {
    EDiag() << "subscript index was null" << show(ast);
    return;
  }

  ExprAST* index = ast->parts[1];
  IntAST* idx = dynamic_cast<IntAST*>(index);
  if (!idx) {
    EDiag() << "SubscriptAST (for now) needs constant int index"
            << show(index);
    return;
  }

  TypeAST* baseType = ast->parts[0]->type;
  if (!baseType) {
    EDiag() << "cannot index into object of null type" << show(ast);
    return;
  }

  const llvm::Type* loweredBaseType = baseType->getLLVMType();
  const llvm::CompositeType* compositeTy = tryGetIndexableType(loweredBaseType);
  if (compositeTy == NULL) {
    EDiag() << "attempt to index into a non-composite type "
            << str(baseType) << show(ast);
    return;
  }

  //std::cout << "Indexing " << *baseType
  //          << " as composite " << *compositeTy << std::endl;

  // Check to see that the given index is valid for this type
  ConstantInt* cidx = llvm::dyn_cast<ConstantInt>(idx->getConstantValue());
  const APInt& vidx = cidx->getValue();

  if (!vidx.isSignedIntN(64)) {
    // an exabyte of memory should be enough for anyone!
    EDiag() << "indices must fit in 64 bits" << show(index);
    return;
  }

  if (!compositeTy->indexValid(cidx) || vidx.isNegative()) {
    EDiag() << "attempt to index composite with invalid index:"
            << show(index);
    return;
  }

  // LLVM doesn't do bounds checking for arrays or vectors, but we do!
  uint64_t numElements = -1;
  if (const llvm::ArrayType* ty
                           = llvm::dyn_cast<llvm::ArrayType>(loweredBaseType)) {
    numElements = ty->getNumElements();
  }

  if (const llvm::VectorType* ty
                          = llvm::dyn_cast<llvm::VectorType>(loweredBaseType)) {
    numElements = ty->getNumElements();
  }

  if (numElements >= 0) {
    uint64_t idx_u64 = vidx.getZExtValue();
    if (idx_u64 >= numElements) {
      EDiag() << "attempt to index array[" << numElements << "]"
              << " with invalid index"
              << show(index);
      return;
    }
  }

  // TODO need to avoid losing typeinfo here
  ast->type = TypeAST::get(compositeTy->getTypeAtIndex(cidx));

  if (this->inAssignLHS) {
    ast->type = TypeAST::get(llvm::PointerType::getUnqual(ast->type->getLLVMType()));
  }
}

void TypecheckPass::visit(SeqAST* ast) {
  bool success = true;
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      if (!ast->parts[i]->type) { success = false; }
    } else {
      std::cerr << "Null expr in SeqAST" << std::endl;
      return;
    }
  }

  if (!success || ast->parts.empty()) {
    EDiag() << "expression block must not be empty" << show(ast);
    return;
  }

  ast->type = ast->parts.back()->type;
}

// HACK HACK HACK - give print_ref special polymorphic type (with hardcoded ret ty)
void givePrintRefPseudoPolymorphicType(CallAST* ast, TypecheckPass* pass) {
 if (ast->parts.size() < 2) {
    EDiag() << "arity mismatch, required one argument but got none"
            << show(ast);
    return;
  }

  ExprAST* arg = ast->parts[1];
  arg->accept(pass);
  if (!arg->type) {
    EDiag() << "print_ref() given arg of no discernable type" << show(arg);
  } else if (!arg->type->getLLVMType()->isPointerTy()) {
    EDiag() << "print_ref() given arg of non-ref type " << str(arg->type)
            << show(arg);
  } else {
    ast->type = TypeAST::get(LLVMTypeFor("i32"));
  }
}

const FunctionType* getFunctionTypeFromClosureStructType(const Type* ty) {
  if (const llvm::StructType* sty = llvm::dyn_cast<llvm::StructType>(ty)) {
    if (const llvm::PointerType* pty
                = llvm::dyn_cast<llvm::PointerType>(sty->getContainedType(0))) {
      return llvm::dyn_cast<llvm::FunctionType>(pty->getElementType());
    }
  }
  std::cerr << "ERROR: failed to get function type from closure struct type: "
            << *ty << std::endl;
  exit(1);
  return NULL;
}

void TypecheckPass::visit(CallAST* ast) {
  ExprAST* base = ast->parts[0];
  if (!base) {
    EDiag() << "called expression was null" << show(ast);
    return;
  }

  base->accept(this);
  TypeAST* baseType = base->type;
  if (baseType == NULL) {
    EDiag() << "called expression had indeterminate type" << show(base);
    return;
  }

  if (isPrintRef(base)) {
    givePrintRefPseudoPolymorphicType(ast, this);
    return;
  }

  FnTypeAST* baseFT = tryExtractCallableType(baseType);
  if (baseFT == NULL) {
    baseFT = originalFunctionTypeForClosureStructType(baseType);
  }

  if (baseFT == NULL) {
    EDiag() << "called expression had non-callable type "
            << str(baseType) << show(base);
    return;
  }

  // Collect args in separate zero-based array for easier counting and indexing
  vector<ExprAST*> args;
  for (size_t i = 1; i < ast->parts.size(); ++i) {
    ExprAST* arg = ast->parts[i];
    if (!arg) {
      EDiag() << "invalid call, arg " << i << " was null" << show(ast);
      return;
    }

    arg->accept(this);
    TypeAST* argTy = arg->type;
    if (!argTy) {
      EDiag() << "call parameter " << i << " had null type" << show(arg);
      return;
    }

    args.push_back(arg);
  }

  size_t numParams = baseFT->getNumParams();
  if (numParams != args.size()) {
    EDiag() << "arity mismatch, " << args.size()
            << " args provided for function of type " << str(baseFT)
            << " taking " << numParams << " args"
            << show(ast);
    return;
  }

  bool success = true;
  for (size_t i = 0; i < numParams; ++i) {
    TypeAST* formalType = baseFT->getParamType(i);
    TypeAST* actualType = args[i]->type;

    if (const FunctionType* fnty
              = llvm::dyn_cast<const FunctionType>(actualType->getLLVMType())) {
      // If we try to use  fa: i32 () in place of ff: void ()*,
      // temporarily give the function fa the type of ff.
      if (isPointerToCompatibleFnTy(formalType->getLLVMType(), fnty)) {
        actualType = formalType;
      } else {
        // Temporarily view a function type as its specific closure type,
        // since the formal arguments will have undergone the same conversion.
        std::cout << "actualtype = " << str(actualType) << std::endl;
        actualType = genericClosureTypeFor(actualType);
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

          if (ExprAST* arg = args[i]) {
             if (ClosureAST* clo = dynamic_cast<ClosureAST*>(arg)) {
               clo->isTrampolineVersion = true;
             } else {
               EDiag() << "LLVM requires literal closure definitions"
                       << " to be given at trampoline creation sites"
                       << show(ast);
               return;
             }
          }
        }
      }
    }

    if (!actualType->canConvertTo(formalType)) {
      success = false;
      EDiag() << "type mismatch, expected " << str(formalType)
              << " but got " << str(actualType)
              << show(args[i]);
    }
  }

  if (success) {
    ast->type = baseFT->getReturnType();
  } else {
    EDiag() << "unable to typecheck call " << show(ast);
  }
}

/// For now, as a special case, simd-vector and array will interpret { 4;i32 }
/// as meaning the same thing as { i32 ; i32 ; i32 ; i32 }
int extractNumElementsAndElementType(unsigned int maxSize, ExprAST* ast,
                                     const Type*& elementType) {
  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  IntAST* first = dynamic_cast<IntAST*>(body->parts[0]);
  IntAST* second = dynamic_cast<IntAST*>(body->parts[1]);
  if (first && !second && body->parts[1]->type) {
    APInt v = first->getAPInt();
    unsigned int n = v.getZExtValue();
    // Sanity check on # elements; nobody (?) wants a billion-element vector
    if (n <= maxSize) {
      elementType = body->parts[1]->type->getLLVMType();
      return n;
    } else {
      EDiag() << "concise simd/array declaration too big" << show(ast);
    }
  }
  return 0;
}

void TypecheckPass::visit(ArrayExprAST* ast) {
  bool success = true;
  std::map<const Type*, bool> fieldTypes;

  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (!body) {
    std::cerr << "Typecheck of array expr failed because ast.parts[0] = "
              << ast->parts[0] << " was not a Seq!" << std::endl;
    return;
  }

  size_t numElements = body->parts.size();
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
    for (size_t i = 0; i < numElements; ++i) {
      const Type* ty =  body->parts[i]->type->getLLVMType();
      if (!ty) {
        EDiag() << "array expr had null constituent type for subexpr " << i
                << show(body->parts[i]);
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

SimdVectorTypeAST* synthesizeSimdVectorType(SimdVectorAST* ast) {
  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (!body) {
    EDiag() << "simd-vector ast.parts[0] = " << str(ast->parts[0])
            << " was not a seq!" << show(ast);
    return NULL;
  }

  size_t numElements = body->parts.size();

  if (!isSmallPowerOfTwo(numElements)) {
    EDiag() << "simd-vector must contain a small power of two"
            << " of elements; got " << numElements
            << show(ast);
    return NULL;
  }

  const Type* elementType = NULL;
  std::map<const Type*, bool> fieldTypes;

  for (size_t i = 0; i < numElements; ++i) {
    const Type* ty =  body->parts[i]->type->getLLVMType();
    if (!ty) {
      EDiag() << "simd-vector expr had null constituent type for subexpr " << i
              << show(body->parts[i]);
      return NULL;
    }
    fieldTypes[ty] = true;
    elementType = ty;
  }

  // TODO This should probably be relaxed eventually; for example,
  // a simd-vector of "small" and "large" int literals should silently be
  // accepted as a simd-vector of "large" ints.
  if (fieldTypes.size() == 0) {
    EDiag() << "simd-vector cannot be empty" << show(ast);
    return NULL;
  }

  if (fieldTypes.size() > 1) {
    std::string s; llvm::raw_string_ostream ss(s);
    std::map<const Type*, bool>::const_iterator it;;
    for (it = fieldTypes.begin(); it != fieldTypes.end(); ++it) {
      ss << "\n\t" << str((*it).first);
    }
    EDiag() << "simd-vector expression had multiple types, found"
            << ss.str() << show(ast);
    return NULL;
  }

  if (!isPrimitiveNumericType(elementType)) {
    EDiag() << "simd-vector must be composed of primitive numeric types"
            << show(ast);
    return NULL;
  }

  return SimdVectorTypeAST::get(
      new LiteralIntTypeAST(numElements, SourceRange::getEmptyRange()),
      TypeAST::get(elementType),
      ast->sourceRange);
}

void TypecheckPass::visit(SimdVectorAST* ast) {
  if (ast->type) return;

  ast->type = synthesizeSimdVectorType(ast);
}

void TypecheckPass::visit(TupleExprAST* ast) {
  SeqAST* body = dynamic_cast<SeqAST*>(ast->parts[0]);
  if (!body) {
    EDiag() << "typechecking tuple failed, body is not a SeqAST" << show(ast);
    return;
  }

  TupleTypeAST* expectedTupleType = NULL;
  if (!ast->typeName.empty()) {
    expectedTupleType
            = dynamic_cast<TupleTypeAST*>(typeScope.lookup(ast->typeName, ""));
  }

  if (expectedTupleType) {
    size_t expectedSize = expectedTupleType->getNumContainedTypes();
    if (expectedSize != body->parts.size()) {
      EDiag() << "mismatch between size of tuple type (" << expectedSize << ")"
              << " and number of expressions in tuple (" << body->parts.size()
              << ")" << show(ast);
      return;
    }
  }

  bool success = true;
  std::vector<TypeAST*> tupleFieldTypes;
  for (size_t i = 0; i < body->parts.size(); ++i) {
    ExprAST* expr = body->parts[i];
    if (!expr) {
      EDiag() << "tuple expr had null component " << i << show(ast);
      break;
    }
    TypeAST* ty = expr->type;
    if (!ty) {
      EDiag() << "tuple had null constituent type for subexpression"
              << show(expr);
      success = false;
      break;
    }

    if (expectedTupleType) {
      TypeAST* expectedType = expectedTupleType->getContainedType(i);
      if (!ty->canConvertTo(expectedType)) {
        EDiag() << "type mismatch at parameter " << i << ", expected "
                << str(expectedType) << " but got " << str(ty)
                << show(expr);
        success = false;
        break;
      }
    }

    tupleFieldTypes.push_back(ty);
  }

  if (success) {
    ast->type = TupleTypeAST::get(tupleFieldTypes);
  }

  return;
}

void TypecheckPass::visit(BuiltinCompilesExprAST* ast) {
  if (ast->parts[0]) {
    ast->parts[0]->accept(this);
    ast->status = (ast->parts[0]->type != NULL)
                      ? ast->kWouldCompile
                      : ast->kWouldNotCompile;
  } else {
    ast->status = ast->kWouldNotCompile;
  }
  ast->type = TypeAST::get(LLVMTypeFor("i1"));
}

