// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"

#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/CompilationContext.h"
#include "parse/FosterUtils.h"

#include "passes/TypecheckPass.h"
#include "passes/PrettyPrintPass.h"
#include "passes/ReplaceTypeTransform.h"

using foster::EDiag;
using foster::dbg;
using foster::show;
using foster::LLVMTypeFor;
using foster::currentErrs;
using foster::currentOuts;

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

bool isIntTypeName(const std::string& s) {
  return s == "int" || s == "i1" || s == "i8"
      || s == "i16" || s == "i32" || s == "i64";
}

// Restriction is that each arg type must match,
// and return types must either match or be */void.
bool canConvertWithVoidWrapper(TypeAST* t1, TypeAST* t2) {
  if (FnTypeAST* ft1 = dynamic_cast<FnTypeAST*>(t1)) {
    if (FnTypeAST* ft2 = dynamic_cast<FnTypeAST*>(t2)) {
      if (ft1->getNumParams() != ft2->getNumParams()) return false;

      if (str(ft1->getReturnType()) != str(ft2->getReturnType())) {
        if (! isVoid(ft2->getReturnType())) return false;
      }

      for (int i = 0; i < ft1->getNumParams(); ++i) {
        if (str(ft1->getParamType(i)) != str(ft2->getParamType(i))) {
          return false;
        }
      }

      return true;
    }
  }
  return false;
}

struct TypecheckPass : public ExprASTVisitor {

  struct Constraints {

    struct TypeASTSet {
      virtual bool contains(TypeAST* ty, Constraints&) = 0;
      virtual std::string describe() = 0;
    };

    struct IntOrIntVectorTypePredicate : public TypeASTSet {
      virtual bool contains(TypeAST* ty, Constraints& constraints) {
        if (TypeVariableAST* tv =  dynamic_cast<TypeVariableAST*>(ty)) {
          ty = constraints.substFind(tv);
        }

        /*if (SimdVectorTypeAST* st = dynamic_cast<SimdVectorTypeAST*>(ty)) {
          ty = st->getContainedType(0);
        }*/

        if (NamedTypeAST* nt = dynamic_cast<NamedTypeAST*>(ty)) {
          return isIntTypeName(nt->getName());
        }

        return false;
      }
      virtual std::string describe() {
        return "int or int vector";
      }
    };

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
      if (tyset->contains(ty, *this)) {
        // don't bother adding it to the set, eagerly ignore it.
      } else {
        tysets.push_back(TypeInSetConstraint(context, ty, tyset));
      }
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
          // If one is a closure type and the other a simple fn type,
          // try matching the closure's fn type with the fn type.
          if (t1->tag == std::string("ClosureType")
           && t2->tag == std::string("FnType")) {
            ClosureTypeAST* ct1 = dynamic_cast<ClosureTypeAST*>(t1);
            TypeAST* ft1 = ct1->getFnType();
            extractTypeConstraints(eConstraintEq, context, ft1, t2, *this);
          } else if (t2->tag == std::string("ClosureType")
                  && t1->tag == std::string("FnType")) {
            ClosureTypeAST* ct2 = dynamic_cast<ClosureTypeAST*>(t2);
            TypeAST* ft2 = ct2->getFnType();
            extractTypeConstraints(eConstraintEq, context, t1, ft2, *this);
          } else if (t1->tag == std::string("FnType")
                  && t2->tag == std::string("RefType")) {
            // Converting a top-level function to a function pointer
            // is trivial, so long as the underlying types match up.
            TypeAST* ft1 = t1;

            RefTypeAST* rt2 = dynamic_cast<RefTypeAST*>(t2);
            // referent type must be concrete/monomorphic (e.g. a C function type)
            TypeAST* ft2 = rt2->getElementType();

            if (string(ft1->tag) == string(ft2->tag)
                && canConvertWithVoidWrapper(ft1, ft2)) {
              // OK!
            } else {
              newLoggedError()
                     << "Unable to unify fn/ref types " << str(ft1) << " and " << str(ft2)
                     << " [" << ft1->tag << " != " << ft2->tag << "]"
                     << " from " << context->tag
                     << foster::show(context);
              // Record the constraint without applying it to the substitution.
              collectEqualityConstraint(context, t1, t2);
            }

          } else if (t1->tag == std::string("ClosureType")
                  && t2->tag == std::string("RefType")) {
            // A closure is compatible with the struct-level
            // representation of the closure.
            ClosureTypeAST* ct1 = dynamic_cast<ClosureTypeAST*>(t1);
            FnTypeAST* ft1 = dynamic_cast<FnTypeAST*>(ct1->getFnType());

            RefTypeAST* rt2 = dynamic_cast<RefTypeAST*>(t2);
            TypeAST* t2 = rt2->getElementType();

            FnTypeAST* ft2 = NULL;
            if (t2->tag == std::string("TupleType")) {
              ft2 = originalFunctionTypeForClosureStructType(t2);
            }

            if (ft1 && ft2) {
              // Ensure that the relative function parameter types match up
              // between R(X, Y) and { R(i8*, X, Y), i8* }.
              extractTypeConstraints(eConstraintEq, context, ft1, ft2, *this);
            } else {
              newLoggedError()
                     << "Unable to unify clo/ref types " << str(t1) << " and " << str(t2)
                     << " [" << t1->tag << " != " << t2->tag << "]"
                     << " from " << context->tag
                     << foster::show(context);
              // Record the constraint without applying it to the substitution.
              collectEqualityConstraint(context, t1, t2);
            }
          } else {
            // If tags aren't equal, then (since neither one is a type var)
            // the equality is immediately false.
            newLoggedError()
                   << "Unable to unify " << str(t1) << " with " << str(t2)
                   << " [" << t1->tag << " != " << t2->tag << "]"
                   << " from " << context->tag
                   << foster::show(context);
            // Record the constraint without applying it to the substitution.
            collectEqualityConstraint(context, t1, t2);
          }
        }
      }
      return true;
    }

    size_t trivialConstraintsDiscarded;
    void discard(ExprAST* context, TypeAST* t1, TypeAST* t2) {
      ++trivialConstraintsDiscarded;
    }

    bool empty() {
      return collectedEqualityConstraints.empty() && tysets.empty();
    }

    void show(llvm::raw_ostream& out, const std::string& lineprefix) {
      out << lineprefix << "==============================\n";
      out << lineprefix << "-------- collected type equality constraints ---------\n";
      for (size_t i = 0; i < collectedEqualityConstraints.size(); ++i) {
        out << lineprefix << collectedEqualityConstraints[i].context->tag
            << "\t" << str(collectedEqualityConstraints[i].t1)
          << " == " << str(collectedEqualityConstraints[i].t2) << "\n";
      }
      out << lineprefix << "-------- type subset constraints ---------\n";
      for (size_t i = 0; i < tysets.size(); ++i) {
        out << lineprefix << tysets[i].context->tag
            << "\t" << str(tysets[i].ty) << "\n";
      }
      out << lineprefix << "-------- current type substitution ---------\n";
      for (TypeSubstitution::iterator it = subst.begin();
                                      it != subst.end(); ++it) {
        out << lineprefix << it->first << "\t" << str(it->second) << "\n";
      }
      out << lineprefix << "==============================\n";
    }

    explicit Constraints() : trivialConstraintsDiscarded(0) {
    }

    typedef std::string TypeVariableName;
    typedef std::map<TypeVariableName, TypeAST*> TypeSubstitution;
    TypeSubstitution subst;
    TypeAST* substFind(TypeVariableAST* tv);
    TypeAST* substFind(const TypeVariableName&);
    TypeVariableAST* findLeader(const std::string& name);

    TypeAST* applySubst(TypeAST* t) {
      ReplaceTypeTransform rtt(subst);
      rtt.subst(t);
      return t;
    }

    bool addEqConstraintToSubstitution(const Constraints::TypeTypeConstraint& ttc);


    vector<foster::EDiag*> errors;
    foster::EDiag& newLoggedError() {
      foster::EDiag* err = new foster::EDiag();
      errors.push_back(err);
      return *err;
    }


    ~Constraints() {
      //for (
    }
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
  } else if (t1->getName() == "i32" && t2->getName() == "i64") {
    discard(t1, t2);
    // OK, can convert.
  } else {
    // The constraint is unsatisfiable...
    constraints.newLoggedError()
           << "Expression cannot have types "
           << t1->getName() << " and " << t2->getName()
           << show(context);
  }
}

void TypeConstraintExtractor::visit(TypeVariableAST* t2) {
  addConstraint(t1_pre, t2);
}

void TypeConstraintExtractor::visit(FnTypeAST* t2) {
  FnTypeAST* t1 = dynamic_cast<FnTypeAST*>(t1_pre);
  int numArgs = t1->getNumParams();
  if (numArgs == t2->getNumParams()) {
    for (int i = 0; i < numArgs; ++i) {
      addConstraint(t1->getParamType(i), t2->getParamType(i));
    }
    addConstraint(t1->getReturnType(), t2->getReturnType());
  } else {
    constraints.newLoggedError()
       << "Unable to match function types taking different numbers of params: "
       << str(t1) << " (" << t1->getNumParams() << ")"
       << "and " << str(t2) << " (" << t2->getNumParams() << ")"
       << show(context);
  }
}

void TypeConstraintExtractor::visit(RefTypeAST* t2) {
  RefTypeAST* t1 = dynamic_cast<RefTypeAST*>(t1_pre);
  addConstraint(t1->getElementType(), t2->getElementType());
}

void TypeConstraintExtractor::visit(TupleTypeAST* t2) {
  TupleTypeAST* t1 = dynamic_cast<TupleTypeAST*>(t1_pre);
  int numTypes = t1->getNumContainedTypes();
  if (numTypes == t2->getNumContainedTypes()) {
    for (int i = 0; i < numTypes; ++i) {
      addConstraint(t1->getContainedType(i), t2->getContainedType(i));
    }
  } else {
    constraints.newLoggedError()
           << "Unable to match tuple types of different sizes: "
           << str(t1) << " (" << t1->getNumContainedTypes() << ")"
           << "and " << str(t2) << " (" << t2->getNumContainedTypes() << ")"
           << show(context);
  }
}

void TypeConstraintExtractor::visit(ClosureTypeAST* t2) {
  ClosureTypeAST* t1 = dynamic_cast<ClosureTypeAST*>(t1_pre);
  addConstraint(t1->getFnType(), t2->getFnType());
}

/*
void TypeConstraintExtractor::visit(SimdVectorTypeAST* t2) {
  SimdVectorTypeAST* t1 = dynamic_cast<SimdVectorTypeAST*>(t1_pre);
  if (t1->getNumElements() == t2->getNumElements()) {
    addConstraint(t1->getContainedType(0), t2->getContainedType(0));
  } else {
    constraints.newLoggedError()
           << "Unable to match simd-vector types of different sizes "
           << str(t1) << " (" << t1->getNumElements() << ")"
           << "and " << str(t2) << " (" << t2->getNumElements() << ")"
           << show(context);
  }
}
*/

void TypeConstraintExtractor::visit(LiteralIntValueTypeAST* t2) {
  LiteralIntValueTypeAST* t1 = dynamic_cast<LiteralIntValueTypeAST*>(t1_pre);
  ASSERT(false) << "type extraction from type int literals not yet implemented.";
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

template <typename K, typename V>
std::vector<K> keysOf(const std::map<K, V>& m) {
  std::vector<K> v;
  for (typename std::map<K, V>::const_iterator it = m.begin(); it != m.end(); ++it) {
    v.push_back(it->first);
  }
  return v;
}

void TypecheckPass::solveConstraints() {
  // Equality constraints have already been solved incrementally,
  // but we might have some stragglers left because we backed off.
  // Push through any stragglers.
  std::vector<std::string> keys(keysOf(constraints.subst));
  for (size_t i = 0; i < keys.size(); ++i) {
    TypeAST* tvs = constraints.substFind(keys[i]);
    if (tvs != NULL) {
      constraints.subst[keys[i]] = tvs;
    } else if (pystring::startswith(keys[i], "intlit")) {
      // Integer literals that are otherwise unconstrained
      // should default to the arbitrary-precision integer type.
      //
      // This comes up in examples such as the following:
      //   __COMPILES if true then { 123 } else { 456 }
      llvm::outs() << "Giving default int type to " << keys[i] << "\n";
      constraints.subst[keys[i]] = foster::TypeASTFor("int");
    }
  }

  // Check type subset constraints
  for (size_t i = 0; i < constraints.tysets.size(); ++i) {
    Constraints::TypeInSetConstraint tsc = constraints.tysets[i];
    TypeAST* ty = constraints.applySubst(tsc.ty);
    if (!tsc.tyset->contains(ty, constraints)) {
      constraints.newLoggedError()
             << "Unsatisfied subset constraint on " << str(ty)
             << ": " << tsc.tyset->describe()
             << show(tsc.context);
    }
  }
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
  ASSERT(tv) << "equality constraints must begin with a type variable! "
             << str(ttc.t1) << "; other: " << str(ttc.t2)
             << foster::show(ttc.context);
  const std::string& tvName = tv->getTypeVariableName();

  TypeAST* tvs = substFind(tv);
  TypeAST* t2 = applySubst(ttc.t2);

  foster::dbg("inference") << str(tv) << " => ... => tvs: "
                           << str(tvs) << " ;; " << str(t2) << "...\n";

  // Have    TypeVar(t1) => ... => non-type-var tvs
  // ttc is  TypeVar(t1) => ttc.t2
  if (!tvs) {
    // t1 doesn't map to anything yet, so enforce the given constraint.
    this->subst[tvName] = t2;
  } else if (tvs == t2)  {
    // Das fine, the chain was short and we have learned nothing.
  } else {
    currentErrs() << "Conflict detected during equality constraint solving!\n"
                  << "\t" << tvName << " cannot be both "
                  << "\n\t\t" << str(tvs) << " and " << str(t2) << ".";
    return false;
  }

  return true;
}

// One small difference from "regular" union/find is that
// because type schemas might need to be updated, we back off one
// layer of indirection when doing path compression.
//
// substFind(TypeVar(a)) takes an incremental substitution like this:
//    TypeVar(a)  =>  TypeVar(b)
//    TypeVar(b)  =>  TypeVar(c)
//    TypeVar(c)  =>  TypeVar(d)
//    TypeVar(d)  =>  sometype
// and updates it to this:
//    TypeVar(a)  =>  TypeVar(d)
//    TypeVar(b)  =>  TypeVar(d)
//    TypeVar(c)  =>  TypeVar(d)
//    TypeVar(d)  =>  sometype
//
// If the chain ends in a type variable, substFind takes this:
//    TypeVar(a)  =>  TypeVar(b)
//    TypeVar(b)  =>  TypeVar(c)
//    TypeVar(c)  =>  TypeVar(d)
//    TypeVar(d)  =>  NULL
// and updates it to this:
//    TypeVar(a)  =>  TypeVar(d)
//    TypeVar(b)  =>  TypeVar(d)
//    TypeVar(c)  =>  TypeVar(d)
//    TypeVar(d)  =>  NULL
//
// The return value is the end of the chain. In the first example,
// that would be sometype ; in the second, NULL.

TypeAST* TypecheckPass::Constraints::substFind(const std::string& name) {
  TypeVariableAST* leader = findLeader(name);
  if (!leader) return NULL;

  TypeAST* next = this->subst[name];
  this->subst[name] = leader;
  while (next) {
    if (TypeVariableAST* nextTv = dynamic_cast<TypeVariableAST*>(next)) {
      if (nextTv == leader) break;
      next = this->subst[nextTv->getTypeVariableName()];
             this->subst[nextTv->getTypeVariableName()] = leader;
    } else break;
  }
  return subst[leader->getTypeVariableName()];
}

TypeAST* TypecheckPass::Constraints::substFind(TypeVariableAST* tv) {
  return substFind(tv->getTypeVariableName());
}

// Given
//    TypeVar(a)  =>  TypeVar(b)
//    TypeVar(b)  =>  TypeVar(x)
//    TypeVar(x)  =>  sometype
//    TypeVar(c)  =>  TypeVar(d)
//    TypeVar(d)  =>  NULL
// the leader of "a" is TypeVar(x), and the leader of "c" is TypeVar(d),
// and the leader of "d" is NULL.
TypeVariableAST* TypecheckPass::Constraints::findLeader(const std::string& name) {
  TypeAST* next = this->subst[name];
  TypeVariableAST* leader = NULL;

  while (next && next != leader) {
    if (TypeVariableAST* nextTv = dynamic_cast<TypeVariableAST*>(next)) {
      leader = nextTv;
    } else break;
    next = this->subst[leader->getTypeVariableName()];
  }

  return leader;
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
    currentOuts() << "Constraints before solving:\n";
    tp.constraints.show(currentOuts(), "\tconstraints:\t");
  }
  tp.solveConstraints();
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

  ExprAST* varOrProto = gScopeLookupAST(ast->name);
  // If this variable names a bound top-level function,
  // the scope contains the appropriate prototype.
  if (varOrProto) {
    ast->type = varOrProto->type;
  }

  if (!ast->type) {
    ast->type = TypeVariableAST::get(ast->name, ast->sourceRange);
  }
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
      constraints.addTypeInSet(ast, innerType,
        new Constraints::IntOrIntVectorTypePredicate());
    } else {
      const llvm::Type* opTy = innerType->getLLVMType();
      ASSERT(opTy);

      if (opTy == LLVMTypeFor("i1")) {
        constraints.newLoggedError()
               << "unary '-' used on a boolean; use 'not' instead" << show(ast);
      } else if (!(opTy->isIntOrIntVectorTy())) {
        constraints.newLoggedError()
               << "operand to unary '-' had non-inty type " << str(opTy) << show(ast);
      }
    }
  } else if (op == "not") {
    if (innerType->isTypeVariable()) { // hack for now, until we get type classes
      constraints.addTypeInSet(ast, innerType,
              new Constraints::IntOrIntVectorTypePredicate());
    } else {
      if (innerType != TypeAST::i(1)) {
        const llvm::Type* opTy = innerType->getLLVMType();
        constraints.newLoggedError()
               << "operand to unary 'not had non-bool type " << str(opTy) << show(ast);
      }
    }
  }
}

bool isBitwiseOp(const std::string& op) {
  return op == "bitand" || op == "bitor" || op == "bitxor"
      || op == "shl" || op == "lshr" || op == "ashr";
}

// requires Lty == Rty
// arith ops   :: ((int, int) -> int) | ((intvector, intvector) -> intvector)
// bitwise ops :: ((int, int) -> int) | ((intvector, intvector) -> intvector)
// cmp ops     :: ((int, int) -> i1 ) | ((intvector, intvector) -> i1       )

void TypecheckPass::visit(BinaryOpExprAST* ast) {
  TypeAST* Lty = ast->parts[ast->kLHS]->type;
  TypeAST* Rty = ast->parts[ast->kRHS]->type;

  if (!Lty || !Rty) { return; }

  const std::string& op = ast->op;

  constraints.addEq(ast, Lty, Rty);
  constraints.addTypeInSet(ast, Lty, new Constraints::IntOrIntVectorTypePredicate());
  constraints.addTypeInSet(ast, Rty, new Constraints::IntOrIntVectorTypePredicate());

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

    EDiag& err = constraints.newLoggedError();
    err    << "formal argument names for function "
           << ast->name << " are not disjoint";
    for (size_t i = 0; i < ast->inArgs.size(); ++i) {
      err  << "\n\t" << ast->inArgs[i]->name;
    }
    err    << show(ast);
    return;
  }

  vector<TypeAST*> argTypes;
  for (size_t i = 0; i < ast->inArgs.size(); ++i) {
    ASSERT(ast->inArgs[i] != NULL);
    VariableAST* arg = (ast->inArgs[i]);

    arg->accept(this);

    TypeAST* ty =  arg->type;
    if (ty == NULL) {
      std::cerr << "Error: proto " << ast->name << " had "
        << "null type for arg '" << arg->name << "'" << "\n";
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
  ASSERT(ast->getProto() != NULL);
  ast->getProto()->accept(this);

  if (ast->getBody() != NULL) {
    gScope.pushExistingScope(ast->getProto()->scope);
    ast->getBody()->accept(this);
    gScope.popExistingScope(ast->getProto()->scope);

    if (ast->getProto()->type && ast->getBody()->type) {
      ast->type = ast->getProto()->type;
    }
  } else {
    // Probably looking at a function type expr. TODO trust but verify
    ast->type = ast->getProto()->type;
  }
}

void TypecheckPass::visit(ClosureAST* ast) {
  ast->fn->accept(this);

  if (ast->hasKnownEnvironment) {
    visitChildren(ast);
  }

  ast->type = new ClosureTypeAST(ast->fn->getProto(), NULL, ast->sourceRange);
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

// In order for copying GC to be able to move GC roots,
// the root must be stored on the stack; thus, new T is implemented
// so that it evaluates to a T** (a stack slot containing a T*)
// instead of a simple T*, which would not be modifiable by the GC.
// In effect, *every* pointer has a mutable concrete representation
// at the implementation level, but not all pointers expose that
// mutability to the source language.
void TypecheckPass::visit(RefExprAST* ast) {
  if (ast->parts[0] && ast->parts[0]->type) {
    ast->type = RefTypeAST::get(ast->parts[0]->type);
  } else {
    const char* problem = ast->parts[0] ? "subexpr with no type" : "no subexpr";
    constraints.newLoggedError()
           << "ref expr had  " << std::string(problem)
           << show(ast);
    ast->type = RefTypeAST::get(TypeVariableAST::get("badref", ast->sourceRange));

  }
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

  constraints.addEq(ast, RefTypeAST::get(T), refT);
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

  constraints.addEq(ast, lhsTy, RefTypeAST::get(rhsTy));

  ast->type = TypeAST::i(32);
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
    TypeAST* sub = constraints.applySubst(tv);
    if (sub && !sub->isTypeVariable()) {
      currentOuts() << "Subscript AST peeking through " << str(tv)
		   << " and replacing it with " << str(sub) << "\n";
      ast->parts[0]->type = baseType = sub;
    } else {
      EDiag() << "SubscriptAST's base type was a type variable (" << str(sub) << " :: " << str(baseType) << ") that"
              << " it couldn't make concrete!" << show(ast);
      constraints.show(currentOuts(), "\tconstraints:\t");
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

  /*if (SimdVectorTypeAST* ty = dynamic_cast<SimdVectorTypeAST*>(baseType)) {
    numElements = ty->getNumElements();
  }*/

  uint64_t idx_u64 = vidx.getZExtValue();

  if (numElements >= 0) {
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
}

void TypecheckPass::visit(SeqAST* ast) {
  bool success = true;
  for (size_t i = 0; i < ast->parts.size(); ++i) {
    if (ast->parts[i]) {
      if (!ast->parts[i]->type) { success = false; }
    } else {
      std::cerr << "Null expr in SeqAST" << "\n";
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
}

const FunctionType* getFunctionTypeFromClosureStructType(const Type* ty) {
  if (const llvm::StructType* sty = llvm::dyn_cast<llvm::StructType>(ty)) {
    if (const llvm::PointerType* pty
                = llvm::dyn_cast<llvm::PointerType>(sty->getContainedType(0))) {
      return llvm::dyn_cast<llvm::FunctionType>(pty->getElementType());
    }
  }
  std::cerr << "ERROR: failed to get function type from closure struct type: "
            << *ty << "\n";
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

  vector<TypeAST*> argTypes;

  FnAST* literalFnBase = dynamic_cast<FnAST*>(base);
  if (literalFnBase) {
    // This is an encoded let-expression   fn (formals) { body }(args).

    // First, inspect just the prototype of the function, to ensure
    // that any un-annotated formals get type variables.
    literalFnBase->getProto()->accept(this);

    // Next, synthesize the args, and constrain the formal and actual
    // parameter types.
    // Finally, use the synthesized types as the annotations on the formals,
    // before inspecting the function body.
    // This is the intuitive way of typechecking a let-binding, which matches
    // both the way a human typechecker would try assigning types, and
    // which also corresponds to "checking" mode of a bidirectional typechecker.
    for (size_t i = 0; i < args.size(); ++i) {
      ExprAST* arg = args[i];
      arg->accept(this);
      if (!arg->type) {
        EDiag() << "call parameter " << i << " had null type" << show(arg);
        return;
      } else { argTypes.push_back(arg->type); }
    }

    size_t maxSafeIndex = (std::min)(args.size(),
                                     literalFnBase->getProto()->inArgs.size());
    for (size_t i = 0; i < maxSafeIndex; ++i) {
      // Ensure that we don't forget the constraint that existed before
      // we overwrote the base function's formal parameter types.
      if (literalFnBase->getProto()->inArgs[i]->type) {
        constraints.addEq(ast, literalFnBase->getProto()->inArgs[i]->type,
                               args[i]->type);
      }
      dynamic_cast<VariableAST*>(literalFnBase->getProto()->inArgs[i])->type =
                                                          args[i]->type;
    }

    literalFnBase->accept(this);
    literalFnBase->type = literalFnBase->getProto()->type; // TODO terrible hack :(
  } else {
    if (ClosureAST* literalClo = dynamic_cast<ClosureAST*>(base)) {
      EDiag() << "\t\tCALL WITH LITERAL CLOSURE BASE: " << show(ast);
    }
    // Otherwise, we should synthesize the base, then check the args.
    base->accept(this);

    for (size_t i = 0; i < args.size(); ++i) {
      ExprAST* arg = args[i];
      arg->accept(this);
      if (!arg->type) {
        EDiag() << "call parameter " << i << " had null type" << show(arg);
        return;
      } else { argTypes.push_back(arg->type); }
    }
  }


  TypeAST* baseType = base->type;
  if (baseType == NULL) {
    EDiag() << "called expression had indeterminate type" << show(base);
    return;
  }

  TypeAST* retTy = TypeVariableAST::get("callret", ast->sourceRange);
  FnTypeAST* actualFnType = FnTypeAST::get(retTy, argTypes, "*");
  constraints.addEq(ast, actualFnType, baseType);

  ast->type = retTy;
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

bool isPrimitiveNumericType(const Type* ty) {
  return ty->isFloatingPointTy() || ty->isIntegerTy();
}
bool isSmallPowerOfTwo(int x) {
  return (x == 2) || (x == 4) || (x == 8) || (x == 16);
}

#if 0
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
#endif

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
    Constraints start(constraints);

    ast->parts[0]->accept(this);
    solveConstraints();

    bool wouldCompileOK = ast->parts[0]->type != NULL
                       && constraints.errors.size() == start.errors.size();

#if 0
    currentOuts() << "BUILTIN COMPILES RESOLUTION: " <<  str(ast->parts[0]->type) << "; "
                 << constraints.errors.size()
                 << " vs " << start.errors.size() << "\n";
     for (size_t i = start.errors.size(); i < constraints.errors.size(); ++i) {
       delete constraints.errors[i];
       constraints.errors[i] = NULL;
     }
#endif

    // Drop errors and constraints generated from within the __compiles__ expr.
    constraints = start;

    ast->status = (wouldCompileOK)
                      ? ast->kWouldCompile
                      : ast->kWouldNotCompile;
  } else {
    ast->status = ast->kWouldNotCompile;
  }
  ast->type = TypeAST::i(1);
}

