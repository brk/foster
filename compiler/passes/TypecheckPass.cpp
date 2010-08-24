// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "parse/FosterAST.h"
#include "parse/CompilationContext.h"
#include "parse/FosterUtils.h"

#include "passes/TypecheckPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ReplaceTypeTransform.h"

using foster::EDiag;
using foster::show;
using foster::LLVMTypeFor;

#include "pystring/pystring.h"

#include "llvm/DerivedTypes.h"
#include "llvm/LLVMContext.h"
#include "llvm/ADT/APInt.h"
#include "llvm/Support/MathExtras.h"

using llvm::Type;
using llvm::Function;
using llvm::FunctionType;
using llvm::IntegerType;
using llvm::Value;
using llvm::ConstantInt;

#include <vector>
#include <map>
#include <string>

using std::vector;

#include "parse/ExprASTVisitor.h"

struct TypeASTSet {
  virtual bool contains(TypeAST* ty) = 0;
};

struct IntOrIntVectorTypePredicate : public TypeASTSet {
  virtual bool contains(TypeAST* ty) { return false; }
};

struct TypecheckPass : public ExprASTVisitor {

  struct Constraints {
    enum ConstraintType { eConstraintEq };
    void extractTypeConstraints(ConstraintType ct,
                                ExprAST* context,
                                TypeAST* t1,
                                TypeAST* t2,
                                Constraints& constraints);

    bool conservativeEqualTypeFilter(TypeAST* t1, TypeAST* t2) {
      // we mainly want to avoid accumulating a large number
      // of trivial i32 = i32 etc constraints...
      if (t1->tag != t2->tag) return false;

      if (NamedTypeAST* nt1 = dynamic_cast<NamedTypeAST*>(t1)) {
        if (NamedTypeAST* nt2 = dynamic_cast<NamedTypeAST*>(t2)) {
          return nt1->getName() == nt2->getName();
        } else { return false; }
      }

      return false; // conservative approximation
    }

    struct TypeTypeConstraint { ExprAST* context; TypeAST* t1; TypeAST* t2;
           TypeTypeConstraint(ExprAST* c, TypeAST* t1, TypeAST* t2) : context(c), t1(t1), t2(t2) {}
    };
    struct TypeInSetConstraint { ExprAST* context; TypeAST* ty; TypeASTSet* tyset;
           TypeInSetConstraint(ExprAST* c, TypeAST* t1, TypeASTSet* ts) : context(c), ty(t1), tyset(ts) {}
    };


    // This constraint type is restricted to only allow sets of concrete types.
    // The upshot is that checking these constraints can be delayed until
    // all other constraints have been collected and solved for, and these
    // constraints don't interfere with resolving type variables.
    vector<TypeInSetConstraint> tysets;
    bool addTypeInSet(ExprAST* context, TypeAST* ty, TypeASTSet* tyset) {
      tysets.push_back(TypeInSetConstraint(context, ty, tyset));
      return true;
    }

    vector<TypeTypeConstraint> convs;
    bool addCanConvertFromTo(ExprAST* context, TypeAST* tyfrom, TypeAST* tyto) {
      if (conservativeEqualTypeFilter(tyfrom, tyto)) return true;

      convs.push_back(TypeTypeConstraint(context, tyfrom, tyto));
      return true;
    }

    vector<TypeTypeConstraint> collectedEqualityConstraints;
    void collectEqualityConstraint(ExprAST* context, TypeAST* t1, TypeAST* t2) {
      collectedEqualityConstraints.push_back(TypeTypeConstraint(context, t1, t2));
    }

    bool addEqUnchecked(ExprAST* context, TypeAST* t1, TypeAST* t2) {
      collectEqualityConstraint(context, t1, t2);
      return addEqConstraintToSubstitution(collectedEqualityConstraints.back());
    }

    bool addEq(ExprAST* context, TypeAST* t1, TypeAST* t2) {
      if (conservativeEqualTypeFilter(t1, t2)) {
        return true;
      }

      bool t1abstract = t1->isTypeVariable();
      bool t2abstract = t2->isTypeVariable();
      if (t1abstract || t2abstract) {
        // Can't extract any juice, so just add constraint as usual
        if (t2abstract && !t1abstract) {
          std::swap(t1, t2); // ensure that t1 is always abstract.
        }
        addEqUnchecked(context, t1, t2);
      } else {
	if (t1->tag == t2->tag) {
          // If the two types have equal tags, extract whatever juice
          // we can. From e.g. (ta, tb) = (tc, td) we'll recursively
          // extract            ta = tc ,  tb = td.
          //
          // From i32 = i32, we'll treat the constraint as trivial,
          // and discard it.
	  extractTypeConstraints(eConstraintEq, context, t1, t2, *this);
	} else {
	  // If tags aren't equal, then (since neither one is a type var)
	  // the equality is immediately false. For now, we'll simply
          // record the purported equality, and complain about it later.
          addEqUnchecked(context, t1, t2);
	}
      }
      return true;
    }

    size_t trivialConstraintsDiscarded;
    void discard(ExprAST* context, TypeAST* t1, TypeAST* t2) {
      ++trivialConstraintsDiscarded;
    }

    bool empty() {
      return collectedEqualityConstraints.empty()
          && convs.empty() && tysets.empty();
    }

    void show(llvm::raw_ostream& out) {
      out << "==============================\n";
      out << "-------- type equality constraints ---------\n";
      for (size_t i = 0; i < collectedEqualityConstraints.size(); ++i) {
        out << "\t" << collectedEqualityConstraints[i].context->tag
            << "\t" << str(collectedEqualityConstraints[i].t1)
          << " == " << str(collectedEqualityConstraints[i].t2) << "\n";
      }
      out << "-------- type conversion constraints ---------\n";
      for (size_t i = 0; i < convs.size(); ++i) {
        out  << "\t" << convs[i].context->tag
            << "\t" << str(convs[i].t1) << " to " << str(convs[i].t2) << "\n";
      }
      out << "-------- type subset constraints ---------\n";
      for (size_t i = 0; i < tysets.size(); ++i) {
        out << "\t" << tysets[i].context->tag
            << "\t" << str(tysets[i].ty) << "\n";
      }
      out << "==============================\n";
    }

    explicit Constraints() : trivialConstraintsDiscarded(0) {
    }

    typedef std::string TypeVariableName;
    typedef std::map<TypeVariableName, TypeAST*> TypeSubstitution;
    TypeSubstitution subst;
    TypeAST* substFind(TypeVariableAST* tv);

    bool addEqConstraintToSubstitution(const Constraints::TypeTypeConstraint& ttc);


    vector<foster::EDiag*> errors;
    void logError(foster::EDiag* err) { errors.push_back(err); }
  };
  Constraints constraints;

  void solveConstraints();
  void applyTypeSubstitution(ExprAST* e);


  explicit TypecheckPass() {}
  ~TypecheckPass() {
  }

  #include "parse/ExprASTVisitor.decls.inc.h"
};


////////////////////////////////////////////////////////////////////

#include "parse/TypeASTVisitor.h"

struct TypeConstraintExtractor : public TypeASTVisitor {
  TypecheckPass::Constraints::ConstraintType ct;
  ExprAST* context;
  TypecheckPass::Constraints& constraints;

  TypeAST* t1_pre;

  TypeConstraintExtractor(
           TypecheckPass::Constraints& constraints,
           TypecheckPass::Constraints::ConstraintType ct,
                          ExprAST* context
                          )
    : ct(ct), context(context), constraints(constraints) {}

  void discard(TypeAST* ta, TypeAST* tb) {
    constraints.discard(context, ta, tb);
  }

  void addConstraint(TypeAST* ta, TypeAST* tb) {
    if (ct == TypecheckPass::Constraints::eConstraintEq) {
      constraints.addEq(context, ta, tb);
    } else {
      ASSERT(false) << "Unknown constraint type while typechecking";
    }
  }

  void addConstraintUnchecked(TypeAST* ta, TypeAST* tb) {
    if (ct == TypecheckPass::Constraints::eConstraintEq) {
      constraints.addEqUnchecked(context, ta, tb);
    } else {
      ASSERT(false) << "Unknown constraint type while typechecking";
    }
  }

  #include "parse/TypeASTVisitor.decls.inc.h"
};

void TypeConstraintExtractor::visit(NamedTypeAST* t2) {
  NamedTypeAST* t1 = dynamic_cast<NamedTypeAST*>(t1_pre);
  if (t1->getName() == t2->getName()) {
    discard(t1, t2); // trivially true!
  } else {
    // The constraint is unsatisfiable...
    EDiag* err = new EDiag();
    (*err) << "Expression cannot have types "
           << t1->getName() << " and " << t2->getName()
           << show(context);
    constraints.logError(err);
  }
}

void TypeConstraintExtractor::visit(TypeVariableAST* t2) {
  addConstraint(t1_pre, t2);
}

void TypeConstraintExtractor::visit(FnTypeAST* t2) {
  FnTypeAST* t1 = dynamic_cast<FnTypeAST*>(t1_pre);
  addConstraintUnchecked(t1, t2); // TODO
}

void TypeConstraintExtractor::visit(RefTypeAST* t2) {
  RefTypeAST* t1 = dynamic_cast<RefTypeAST*>(t1_pre);
  addConstraint(t1->getElementType(), t2->getElementType());
}

void TypeConstraintExtractor::visit(TupleTypeAST* t2) {
  TupleTypeAST* t1 = dynamic_cast<TupleTypeAST*>(t1_pre);
  addConstraintUnchecked(t1, t2); // TODO
}

void TypeConstraintExtractor::visit(ClosureTypeAST* t2) {
  ClosureTypeAST* t1 = dynamic_cast<ClosureTypeAST*>(t1_pre);
  addConstraintUnchecked(t1, t2); // TODO
}

void TypeConstraintExtractor::visit(SimdVectorTypeAST* t2) {
  SimdVectorTypeAST* t1 = dynamic_cast<SimdVectorTypeAST*>(t1_pre);
  addConstraintUnchecked(t1, t2); // TODO
}

void TypeConstraintExtractor::visit(LiteralIntValueTypeAST* t2) {
  LiteralIntValueTypeAST* t1 = dynamic_cast<LiteralIntValueTypeAST*>(t1_pre);
  addConstraintUnchecked(t1, t2); // TODO
}

void TypecheckPass::Constraints::extractTypeConstraints(
     TypecheckPass::Constraints::ConstraintType ct,
				 ExprAST* context,
				 TypeAST* t1,
				 TypeAST* t2,
				 Constraints& constraints) {
  TypeConstraintExtractor tce(constraints, ct, context);
  tce.t1_pre = t1; t2->accept(&tce);
}

////////////////////////////////////////////////////////////////////

void TypecheckPass::solveConstraints() {
  // Equality constraints have already been solved incrementally.
  // TODO process deferred constraints
}

// A set of equality constraints forms an undirected graph,
// where the nodes are type variables, types, and type schemas,
// and the edges are the constraints collected during typechecking.
//
// From this graph, we wish to derive a substitution mapping
// type variables to types and type schemas.
//
// One nifty way of efficiently doing so, incrementally, is to
// treat the problem as a variation of union-find, where connected
// nodes form an equivalence class. The variation is that when
// selecting representative elements, concrete types always take
// precedence over abstract types. This makes it trivial to detect
// when a type conflict exists: two concrete types will be unioned.
// If that occurs, we can search the graph to find the minimum-length
// path between the concrete types.
bool TypecheckPass::Constraints::addEqConstraintToSubstitution(
         const TypecheckPass::Constraints::TypeTypeConstraint& ttc) {

  TypeVariableAST* tv = dynamic_cast<TypeVariableAST*>(ttc.t1);
  ASSERT(tv) << "equality constraints must begin with a type variable!";
  const std::string& tvName = tv->getTypeVariableName();
  
  TypeAST* tvs = substFind(tv);
  // Because substFind does path compression, we know
  // that tvs is not a type variable.
  ASSERT(!(tvs && tvs->isTypeVariable()))
    << "substFind should do path compression and not"
    << " return type variables! Saw " << str(tv) << " to " << str(tvs);

  if (!tvs) {
    this->subst[tvName] = ttc.t2;
  } else if (tvs == ttc.t2)  {
    // Das fine... 
  } else {
    llvm::errs() << "Conflict detected during equality constraint solving!\n"
	<< "\t" << tvName << " cannot be both "
	<< "\n\t\t" << str(tvs) << " and " << str(ttc.t2) << ".";
    return false;
  }
//  llvm::outs() << ttc.context->tag << "\t" << str(ttc.t1) << " == " << str(ttc.t2) << "\n";
  return true;
}

// One small difference from "regular" union/find is that
// because type schemas might need to be updated, we back off one
// layer of indirection when doing path compression.
TypeAST* TypecheckPass::Constraints::substFind(TypeVariableAST* tv) {
  TypeVariableAST* leader = tv;
  while (true) {
    const std::string& tvName = leader->getTypeVariableName();
    TypeAST* next = this->subst[tvName];
    if (!next || next == leader) { break; }

    if (TypeVariableAST* nextTv = dynamic_cast<TypeVariableAST*>(next)) {
      leader = nextTv;
    } else { break; }
  }

  // Path compression
  while (true) {
    const std::string& tvName = tv->getTypeVariableName();
    TypeAST* next = this->subst[tvName];
    if (!next) { break; }
    if (next == leader) {
      // We'd like to maintain the invariant that we never
      // return a type variable, so we break self-loops.
      this->subst[tvName] = NULL;
      break;
    }
    if (TypeVariableAST* nextTv = dynamic_cast<TypeVariableAST*>(next)) {
      tv = nextTv;
      this->subst[tvName] = leader;
      llvm::outs() << "\t" << tvName << " -> " << str(leader)
                 << " instead of " << str(next) << "\n";
    } else { break; }
  }

  return subst[leader->getTypeVariableName()];
}

void TypecheckPass::applyTypeSubstitution(ExprAST* e) {
  ReplaceTypeTransform rtt(constraints.subst);
  foster::replaceTypesIn(e, rtt);
}

namespace foster {

// returns true if typechecking succeeded
bool typecheck(ExprAST* e) {
  TypecheckPass tp; e->accept(&tp);
  if (tp.constraints.empty()) {
    return true;
  }

  if (!tp.constraints.empty()) {
    llvm::outs() << "Constraints before solving:\n";
    tp.constraints.show(llvm::outs());
  }
  tp.solveConstraints();
#if 0
    if (!constraints.empty()) {
      llvm::outs() << "Constraints after solving:\n";
      constraints.show(llvm::outs());
    }
#endif
  tp.applyTypeSubstitution(e);
  
  bool noProblemsTypechecking = tp.constraints.errors.empty();
  for (size_t i = 0; i < tp.constraints.errors.size(); ++i) {
    EDiag* e = tp.constraints.errors[i];
    tp.constraints.errors[i] = NULL;
    delete e; // dtor triggers emission of stored error message.
  }

  return noProblemsTypechecking;
}

} // namespace foster

////////////////////////////////////////////////////////////////////

// A bool is a bit, which is a one-bit integer.
void TypecheckPass::visit(BoolAST* ast) { ast->type = TypeAST::i(1); }

// Integer literals have a "tightest-possible" bit width assigned to them
// during parsing, based on how many bits it takes to represent the literal.
// So we just make sure that we have a type, and that it's an int type.
void TypecheckPass::visit(IntAST* ast) {
  ASSERT(ast->type
      && ast->type->getLLVMType()
      && ast->type->getLLVMType()->isIntegerTy());
}


void TypecheckPass::visit(VariableAST* ast) {
  if (ast->type) { return; }
  
  //EDiag() << "variable " << ast->name << " has no type!" << show(ast);
  ast->type = TypeVariableAST::get(ast->name, ast->sourceRange);
}

// unary negate :: (int -> int) | (intvector -> intvector)
// unary not    :: i1 -> i1

void TypecheckPass::visit(UnaryOpExprAST* ast) {
  TypeAST* innerType = ast->parts[0]->type;
  if (!innerType) {
    return;
  } else {
    ast->type = innerType;
  }

  const std::string& op = ast->op;

  if (op == "-") {
    if (innerType->isTypeVariable()) { // hack for now, until we get type classes
      constraints.addTypeInSet(ast, innerType, new IntOrIntVectorTypePredicate());
    } else {
      const llvm::Type* opTy = innerType->getLLVMType();
      ASSERT(opTy);

      if (opTy == LLVMTypeFor("i1")) {
	EDiag* err = new EDiag();
	(*err) << "unary '-' used on a boolean; use 'not' instead" << show(ast);
	constraints.logError(err);
      } else if (!(opTy->isIntOrIntVectorTy())) {
	EDiag* err = new EDiag();
	(*err) << "operand to unary '-' had non-inty type " << str(opTy) << show(ast);
	constraints.logError(err);
      }
    }
  } else if (op == "not") {
    if (innerType->isTypeVariable()) { // hack for now, until we get type classes
      constraints.addTypeInSet(ast, innerType, new IntOrIntVectorTypePredicate());
    } else {
      if (innerType != TypeAST::i(1)) {
        const llvm::Type* opTy = innerType->getLLVMType();
	EDiag* err = new EDiag();
	(*err) << "operand to unary 'not had non-bool type " << str(opTy) << show(ast);
	constraints.logError(err);
      }
    }
  }
}

bool isBitwiseOp(const std::string& op) {
  return op == "bitand" || op == "bitor" || op == "bitxor"
      || op == "shl" || op == "lshr" || op == "ashr";
}

// requires Lty convertible to Rty
// arith ops   :: ((int, int) -> int) | ((intvector, intvector) -> intvector)
// bitwise ops :: ((int, int) -> int) | ((intvector, intvector) -> intvector)
// cmp ops     :: ((int, int) -> i1 ) | ((intvector, intvector) -> i1       )

void TypecheckPass::visit(BinaryOpExprAST* ast) {
  TypeAST* Lty = ast->parts[ast->kLHS]->type;
  TypeAST* Rty = ast->parts[ast->kRHS]->type;

  if (!Lty || !Rty) { return; }

  const std::string& op = ast->op;

  constraints.addCanConvertFromTo(ast, Lty, Rty);
  constraints.addTypeInSet(ast, Lty, new IntOrIntVectorTypePredicate());
  constraints.addTypeInSet(ast, Rty, new IntOrIntVectorTypePredicate());

  if (isCmpOp(op)) {
    ast->type = TypeAST::i(1);
  } else {
    ast->type = Rty;
  }
}

bool areNamesDisjoint(const std::vector<VariableAST*>& vars) {
  std::map<std::string, bool> seen;
  for (size_t i = 0; i < vars.size(); ++i) {
    seen[vars[i]->name] = true;
  }
  return seen.size() == vars.size();
}

bool isTopLevel(PrototypeAST* ast) {
  bool rv = ast && ast->parent && !ast->parent->parent;
  std::cout << "isTopLevel " << ast->name << ": " << rv << std::endl;
  return rv;
}

const char* getCallingConvention(PrototypeAST* ast) {
  if (ast->name == "main"
  ||  pystring::startswith(ast->name, "llvm.")
  ||  pystring::startswith(ast->name, "__voidReturningVersionOf__")) {
    return "ccc";
  } else {
    return "fastcc";
  }
}

// * Ensures names of function parameters are disjoint
// * Ensures that all args exist and (for now) have explicit types.
// * Gives the prototype a FnTypeAST type.
void TypecheckPass::visit(PrototypeAST* ast) {
  if (!areNamesDisjoint(ast->inArgs)) {
    EDiag d; d << "formal argument names for function "
              << ast->name << " are not disjoint";
    for (size_t i = 0; i < ast->inArgs.size(); ++i) {
      d << "\n\t" << ast->inArgs[i]->name;
    }
      d       << show(ast);
    return;
  }

  vector<TypeAST*> argTypes;
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    ASSERT(ast->inArgs[i] != NULL);
    VariableAST* arg = (ast->inArgs[i]);

    arg->accept(this);
    /*
    if (!arg->type) {
      arg->type = TypeVariableAST::get(arg->name, arg->sourceRange);
      std::cout << "Adding type annotation to arg " << arg->name << ": " << arg->type << std::endl;
    } else {

    }
*/
    TypeAST* ty =  arg->type;
    if (ty == NULL) {
      std::cerr << "Error: proto " << ast->name << " had "
        << "null type for arg '" << arg->name << "'" << std::endl;
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
    ast->type = FnTypeAST::get(ast->resultTy, argTypes,
                               getCallingConvention(ast));
  }
}

void TypecheckPass::visit(FnAST* ast) {
  std::cout << "type checking FnAST" << std::endl;
  ASSERT(ast->proto != NULL);
  ast->proto->accept(this);

  if (ast->body != NULL) {
    ast->body->accept(this);

    if (ast->proto->type && ast->body->type) {
      ast->type = ast->proto->type;
    }
  } else {
    // Probably looking at a function type expr. TODO trust but verify
    ast->type = ast->proto->type;
  }
}

void TypecheckPass::visit(ClosureAST* ast) {
  std::cout << "Type Checking closure AST node " << (*ast) << " ;; " << ast->fn << "; "
            << ast->hasKnownEnvironment << std::endl;

  ast->fn->accept(this);

  if (ast->hasKnownEnvironment) {
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
    if (FnTypeAST* ft = tryExtractCallableType(ast->fn->type)) {
      ast->type = genericClosureTypeFor(ft);
      EDiag() << "ClosureTypeAST fn typechecking converted "
              << str(ft) << " to " << str(ast->type) << show(ast);
    } else {
      EDiag() << "Error! 282 Function passed to closure"
              << "does not have function type!" << show(ast);
    }
  }

  llvm::outs() << "After type checking closure, have: \n";
  foster::prettyPrintExpr(ast, llvm::outs(), 55);
  llvm::outs() << "\n";
}

void TypecheckPass::visit(NamedTypeDeclAST* ast) {
  return;
}

void TypecheckPass::visit(ModuleAST* ast) {
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    ast->parts[i]->accept(this);
    if (ast->parts[i]->type) {
      ast->type = ast->parts[i]->type;
    }
  }
}

// type(testExpr) == i1
// type(thenExpr) == type(elseExpr)
// type(ifExpr) == type(thenExpr)
void TypecheckPass::visit(IfExprAST* ast) {
  ExprAST* testExpr = ast->getTestExpr();
  ExprAST* thenExpr = ast->getThenExpr();
  ExprAST* elseExpr = ast->getElseExpr();
  ASSERT(testExpr != NULL);

  testExpr->accept(this);
  thenExpr->accept(this);
  elseExpr->accept(this);

  constraints.addEq(testExpr, testExpr->type, TypeAST::i(1));
  constraints.addEq(ast,      thenExpr->type, elseExpr->type);
  ast->type = thenExpr->type;

#if 0
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
#endif
}

// ast = for VAR in START to END by INCR do BODY
// type(start) == i32
// type(start) == type(var)
// type(start) == type(end)
// type(start) == type(incr)
void TypecheckPass::visit(ForRangeExprAST* ast) {
  visitChildren(ast);
  ast->var->accept(this);

  constraints.addEq(ast, ast->getStartExpr()->type, TypeAST::i(32));
  // note: this "should" be a test for assignment compatibility, not strict equality.
  constraints.addEq(ast, ast->getStartExpr()->type, ast->var->type);
  constraints.addEq(ast, ast->getStartExpr()->type, ast->getEndExpr()->type);
  constraints.addEq(ast, ast->getStartExpr()->type, ast->getIncrExpr()->type);
  ast->type = TypeAST::i(32);

#if 0
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

  ast->type = TypeAST::i(32);
#endif
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
  return;
}

// TODO currently unused
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

// In order for copying GC to be able to move GC roots,
// the root must be stored on the stack; thus, new T is implemented
// so that it evaluates to a T** (a stack slot containing a T*)
// instead of a simple T*, which would not be modifiable by the GC.
// In effect, *every* pointer has a mutable concrete representation
// at the implementation level, but not all pointers expose that
// mutability to the source language.
void TypecheckPass::visit(RefExprAST* ast) {
  ASSERT(ast->parts[0] && ast->parts[0]->type);

  ast->type = RefTypeAST::get(ast->parts[0]->type);
}

// G |- e : ref(T)
// ---------------
// deref(e) : T
//
void TypecheckPass::visit(DerefExprAST* ast) {
  ASSERT(ast->parts[0]->type) << "Need arg to typecheck deref!";
  ExprAST* e = ast->parts[0];

  TypeAST* refT = e->type;
  TypeAST* T = TypeVariableAST::get("deref", ast->sourceRange);

  constraints.addEq(ast, RefTypeAST::get(T, false), refT);
  ast->type = T;
}

// G |- v : T
// G |- x : ref(T)
// ---------------
// (set x = v) : i32
//
void TypecheckPass::visit(AssignExprAST* ast) {
  TypeAST* lhsTy = ast->parts[0]->type;
  TypeAST* rhsTy = ast->parts[1]->type;

  constraints.addEq(ast, lhsTy, RefTypeAST::get(rhsTy, false));

  ast->type = TypeAST::i(32);

#if 0
  if (RefTypeAST* plhsTy = dynamic_cast<RefTypeAST*>(lhsTy)) {
    lhsTy = plhsTy->getElementType();
    if (rhsTy->canConvertTo(lhsTy)) {
      ast->type = TypeAST::i(32);
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
#endif
}

// Returns aggregate (struct, array, union) and vector types directly,
// and returns the underlying aggregate type for pointer-to-aggregate.
// Returns NULL in other cases.
IndexableTypeAST* tryGetIndexableType(TypeAST* ty) {
  if (RefTypeAST* r = dynamic_cast<RefTypeAST*>(ty)) {
    ty = r->getElementType();
  }

  return dynamic_cast<IndexableTypeAST*>(ty);
}

// base[index]
//
// For now, we require explicit annotations to ensure typeability
// of subscript indexing without needing type classes or other
// overloading mechanisms.
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
  
  if (dynamic_cast<RefTypeAST*>(baseType)) {
    EDiag() << "cannot index into ref types" << show(ast);
    return; 
  }

  if (TypeVariableAST* tv = dynamic_cast<TypeVariableAST*>(baseType)) {
    TypeAST* sub = constraints.substFind(tv);
    if (sub && !sub->isTypeVariable()) {
      llvm::outs() << "Subscript AST peeking through " << str(tv)
		   << " and replacing it with " << str(sub) << "\n";
      ast->parts[0]->type = baseType = sub;
    } else {
      EDiag() << "SubscriptAST's base type was a type variable that"
              << " it couldn't make concrete!" << show(ast);
      ASSERT(false);
    }
  }

  // Check to see that the given index is valid for this type
  ConstantInt* cidx = llvm::dyn_cast<ConstantInt>(idx->getConstantValue());
  const APInt& vidx = cidx->getValue();

  if (!vidx.isSignedIntN(64)) {
    // an exabyte of memory should be enough for anyone!
    EDiag() << "indices must fit in 64 bits" << show(index);
    return;
  }

  
  IndexableTypeAST* compositeTy = tryGetIndexableType(baseType);
  const llvm::ArrayType* arrayTy = NULL;
              //llvm::dyn_cast<llvm::ArrayType>(baseType->getLLVMType());
  if (!compositeTy && !arrayTy) {
    EDiag() << "attempt to index into a non-indexable type "
            << str(baseType) << show(ast);
    return;
  }

  // LLVM doesn't do bounds checking for arrays or vectors, but we do!
  uint64_t numElements = -1;
  bool isNonArrayWithLargeIndex = false;

  if (arrayTy) {
    numElements = arrayTy->getNumElements();
  } else {
    isNonArrayWithLargeIndex = !vidx.isIntN(32);
  }
  
  if (vidx.isNegative() || isNonArrayWithLargeIndex) {
    EDiag() << "attempt to index composite with invalid index:"
            << show(index);
    return;
  }
  
  if (SimdVectorTypeAST* ty = dynamic_cast<SimdVectorTypeAST*>(baseType)) {
    numElements = ty->getNumElements();
  }

  uint64_t idx_u64 = vidx.getZExtValue();
  
  if (numElements >= 0) {
    uint64_t idx_u64 = vidx.getZExtValue();
    if (idx_u64 >= numElements) {
      EDiag() << "attempt to index array[" << numElements << "]"
              << " with invalid index"
              << show(index);
      return;
    }
  }

  int64_t literalIndexValue = vidx.getSExtValue();
  if (!compositeTy->indexValid(literalIndexValue)) {
    EDiag() << "attmpt to index composite with invalid index " << literalIndexValue
            << show(ast);
    return;
  }

  ast->type = compositeTy->getContainedType(literalIndexValue);

  if (this->inAssignLHS) {
    ast->type = RefTypeAST::get(ast->type, /*nullable*/ false);
  }
}

void TypecheckPass::visit(SeqAST* ast) {
  bool success = true;
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      if (!ast->parts[i]->type) { success = false; }
    } else {
      std::cerr << "Null expr in SeqAST" << std::endl;
      ast->type = TypeAST::i(32);
      return;
    }
  }

  //ASSERT(success) << "found ast nodes with null types in SeqAST";

  if (ast->parts.empty()) {
    EDiag() << "expression block must not be empty" << show(ast);
    ast->type = TypeAST::i(32);
  } else if (ast->parts.back() && ast->parts.back()->type) {
    ast->type = ast->parts.back()->type;
  } else {
    EDiag() << "non-empty expression block with no usable type!" << show(ast);
    ast->type = TypeAST::i(32);
  }
}

// HACK HACK HACK - give print_ref special polymorphic type (with hardcoded ret ty)
//
// G |- e : ref(T)
// ----------
// G |- (print_ref(e)) : i32
void givePrintRefPseudoPolymorphicType(CallAST* ast, TypecheckPass* pass) {
  ast->type = TypeAST::i(32);

 if (ast->parts.size() < 2) {
    EDiag() << "arity mismatch, required one argument for print_ref() but got none"
            << show(ast);
    return;
  }

  ExprAST* arg = ast->parts[1];
  arg->accept(pass);
  
  if (!arg->type) {
    EDiag() << "print_ref() given arg of no discernable type" << show(arg);
    return;
  }

  TypeAST* refT = RefTypeAST::get(TypeVariableAST::get("printref", arg->sourceRange));
  
  pass->constraints.addEq(ast, arg->type, refT);

#if 0
  if (!arg->type->getLLVMType()->isPointerTy()) {
    EDiag() << "print_ref() given arg of non-ref type " << str(arg->type)
            << show(arg);
  }
#endif
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

  if (isPrintRef(base)) {
    givePrintRefPseudoPolymorphicType(ast, this);
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
    args.push_back(arg);
  }


  FnAST* literalFnBase = dynamic_cast<FnAST*>(base);
  if (literalFnBase) {
    // If this is an encoded let-expression   fn (formals) { body }(args)
    // we should synthesize the args first, then use the synthesized types
    // as the annotations on the formals.
    for (size_t i = 0; i < args.size(); ++i) {
      ExprAST* arg = args[i];
      arg->accept(this);
      if (!arg->type) {
        EDiag() << "call parameter " << i << " had null type" << show(arg);
        return;
      }
    }

    size_t maxSafeIndex = (std::min)(args.size(), literalFnBase->proto->inArgs.size());
    std::cout << "max safe index: " << maxSafeIndex << "\n";
    for (size_t i = 0; i < maxSafeIndex; ++i) {
      dynamic_cast<VariableAST*>(literalFnBase->proto->inArgs[i])->type = args[i]->type;
    }

    base->accept(this);
  } else {
    // Otherwise, we should synthesize the base, then check the args.
    base->accept(this);

    for (size_t i = 0; i < args.size(); ++i) {
      ExprAST* arg = args[i];
      arg->accept(this);
      if (!arg->type) {
        EDiag() << "call parameter " << i << " had null type" << show(arg);
        return;
      }
    }
  }


  TypeAST* baseType = base->type;
  if (baseType == NULL) {
    EDiag() << "called expression had indeterminate type" << show(base);
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

  size_t numParams = baseFT->getNumParams();
  if (numParams != args.size()) {
    EDiag() << "arity mismatch, " << args.size()
            << " args provided for function of type " << str(baseFT)
            << " taking " << numParams << " args"
            << show(ast);
    return;
  }

  for (size_t i = 0; i < numParams; ++i) {
    TypeAST* formalType = baseFT->getParamType(i);
    TypeAST* actualType = args[i]->type;
    constraints.addCanConvertFromTo(ast, actualType, formalType);
  }

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
        std::cout << "TYPECHECK CallAST converting " << *fnty
                  << " to " << str(actualType->getLLVMType()) << std::endl;
        std::cout << "\t for formal type:\t" << str(formalType->getLLVMType())
                  << std::endl;
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
  }

  ast->type = baseFT->getReturnType();
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

#if 0
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
#endif

bool isPrimitiveNumericType(const Type* ty) {
  return ty->isFloatingPointTy() || ty->isIntegerTy();
}
bool isSmallPowerOfTwo(int x) {
  return (x == 2) || (x == 4) || (x == 8) || (x == 16);
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

  TypeAST* elementType = NULL;
  std::map<const Type*, TypeAST*> fieldTypes;

  for (size_t i = 0; i < numElements; ++i) {
    TypeAST* ty =  body->parts[i]->type;
    const Type* lty = (ty) ? ty->getLLVMType() : NULL;
    if (!ty || !lty) {
      EDiag() << "simd-vector expr had null constituent type for subexpr " << i
              << show(body->parts[i]);
      return NULL;
    }
    fieldTypes[lty] = ty;
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
    std::map<const Type*, TypeAST*>::const_iterator it;;
    for (it = fieldTypes.begin(); it != fieldTypes.end(); ++it) {
      ss << "\n\t" << str((*it).first);
    }
    EDiag() << "simd-vector expression had multiple types, found"
            << ss.str() << show(ast);
    return NULL;
  }

  if (!isPrimitiveNumericType(elementType->getLLVMType())) {
    EDiag() << "simd-vector must be composed of primitive numeric types"
            << show(ast);
    return NULL;
  }

  return SimdVectorTypeAST::get(
      LiteralIntValueTypeAST::get(numElements, SourceRange::getEmptyRange()),
      elementType,
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
  ast->type = TypeAST::i(1);
}

