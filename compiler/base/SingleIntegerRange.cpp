// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/SingleIntegerRange.h"

#include <map>
#include <set>
#include <vector>

#include "llvm/ADT/APInt.h"
#include "llvm/Support/raw_ostream.h"

#include "pystring/pystring.h"

using llvm::raw_ostream;

namespace foster {
  
  struct SingleIntegerRangeVariable;
  
struct Valuation {
  std::map<SingleIntegerRangeVariable*, SingleIntegerRange*> p;
  
  virtual SingleIntegerRange* evaluate(SingleIntegerRangeExpr* e) {
    return e->evaluate(this);
  }
  
  bool satisfies(SingleIntegerRangeConstraint* c); 
};


SingleIntegerRangeExpr* mult(const llvm::APInt& n,
                             SingleIntegerRangeVariable* v);
const llvm::APInt getAPInt(int n);

////////////////////////////////////////////////////////////////////

struct IntOrInf {
  int inf; // -1 = -inf, +1 = +inf, 0 = finite
  llvm::APInt n;
  
  IntOrInf(int inf, const llvm::APInt& m) : inf(inf), n(m) {}
};

raw_ostream& operator <<(raw_ostream& out, const IntOrInf& i) {
  if (i.inf == 0) {       out << i.n;
  } else if (i.inf < 0) { out << "-inf";
  } else {                out << "+inf";  }
  return out;
}

bool operator<(const IntOrInf& x, const IntOrInf& y) {
  if (x.inf < y.inf) return true;
  if (y.inf < x.inf) return false;
  return x.n.slt(y.n);
}

bool operator<=(const IntOrInf& x, const IntOrInf& y) {
  if (x.inf < y.inf) return true;
  if (y.inf < x.inf) return false;
  return x.n.sle(y.n);
}

bool operator==(const IntOrInf& x, const IntOrInf& y) {
  if (x.inf == y.inf) return x.n == y.n;
  return false;
}

// sup = lub = least upper bound ~~ max
IntOrInf sup(const IntOrInf& x, const IntOrInf& y) {
  return (x < y) ? y : x;
}

// ~~ min
IntOrInf inf(const IntOrInf& x, const IntOrInf& y) {
  return (x < y) ? x : y;
}

IntOrInf operator*(const IntOrInf& x, const llvm::APInt& n) {
  if (x.inf != 0) return x;
  else return IntOrInf(x.inf, x.n * n);
}

IntOrInf operator-(const IntOrInf& x) {
  if (x.inf != 0)
       return IntOrInf(-x.inf, x.n);
  else return IntOrInf(x.inf, -x.n);
}

IntOrInf operator+(const IntOrInf& x, const IntOrInf& y) {
  if (x.inf == y.inf) {
    IntOrInf(x.inf, x.n + y.n);
  } else if (x.inf < y.inf) {
    return y;
  } else if (x.inf > y.inf) {
    return x;
  }  
}

////////////////////////////////////////////////////////////////////

SingleIntegerRange* inverse(SingleIntegerRange* r);

// { [l, u] | l in (ZZ U {-inf}) and u in (ZZ U +inf) and l <= u }
struct SingleIntegerRange : public SingleIntegerRangeExpr {
  IntOrInf lo;
  IntOrInf hi;
  
  // Empty ranges are those that contain no finite elements,
  // which means either their upper is less than their lower,
  // or their upper and lower coincide and are both + or - infinity.
  bool isEmpty() const {
    return (hi < lo) || (hi == lo && hi.inf != 0);
  }
  static SingleIntegerRange* get(const IntOrInf& l, const IntOrInf& u);
  static SingleIntegerRange* getTop();
  
  virtual SingleIntegerRange* evaluate(Valuation* p) { return this; }
  
  virtual raw_ostream& dump(raw_ostream& out) const {
    if (isEmpty()) {
      return out << "[" <<      "empty"     << "]";
    } else {
      return out << "[" << lo << ", " << hi << "]";
    }
    
  }
  
  virtual SingleIntegerRangeExpr* negate() {
    return inverse(this);
  }
  
  
  virtual void variablesUsed(std::set<SingleIntegerRangeVariable*>& vars) {
    // none
  }

private:
  SingleIntegerRange(const IntOrInf& l, const IntOrInf& u) : lo(l), hi(u) {}
};

SingleIntegerRange* getTopRange() {
  return SingleIntegerRange::getTop();
}

SingleIntegerRange* SingleIntegerRange::getTop() {
  static SingleIntegerRange* top = NULL;
  if (!top) {
    top = get(IntOrInf(-1, getAPInt(1234567)),
              IntOrInf(+1, getAPInt(1234567)));
  }
  return top;
}

SingleIntegerRange* SingleIntegerRange::get(const IntOrInf& l,
                                            const IntOrInf& u) {
  return new SingleIntegerRange(l, u); 
}

bool isEmpty(SingleIntegerRange* r) { return r->isEmpty(); }

SingleIntegerRange* getConstantRange(int x, int y) {
  return SingleIntegerRange::get(
    IntOrInf(0, getAPInt(x)),
    IntOrInf(0, getAPInt(y)));
}

SingleIntegerRange* getConstantRange(int x) {
  return getConstantRange(x, x);
}

SingleIntegerRange* getMinRange(int x) {
  return SingleIntegerRange::get(
    IntOrInf(0,  getAPInt(x)),
    IntOrInf(+1, getAPInt(x)));
}

SingleIntegerRange* getMaxRange(int x) {
  return SingleIntegerRange::get(
    IntOrInf(-1, getAPInt(x)),
    IntOrInf(0,  getAPInt(x)));
}

////////////////////////////////////////////////////////////////////

struct SingleIntegerRangeVariable : public SingleIntegerRangeExpr {
  const std::string* name;
  // Returns a unique pointer for each string
  static SingleIntegerRangeVariable* get(const std::string* name);
  
  virtual SingleIntegerRange* evaluate(Valuation* p) { return p->p[this]; }
  
  virtual raw_ostream& dump(raw_ostream& out) const {
    return out << *name; 
  }
  
  bool isNeutral() {
    // non-netural variables are like "___!+" or "___!-"
    return name->size() < 3 || (*name)[name->size() - 2] != '!';
  }
  
  SingleIntegerRangeVariable* getPositiveVersion() {
    return getVariable(*name + "!+");
  }
  
  SingleIntegerRangeVariable* getNegativeVersion() {
    return getVariable(*name + "!-");
  }
  
  virtual SingleIntegerRangeExpr* negate() {
    return getNegativeVersion();
  }
  
  virtual void variablesUsed(std::set<SingleIntegerRangeVariable*>& vars) {
    vars.insert(this);
  }
  
private:
  SingleIntegerRangeVariable(const std::string* name) : name(name) {}
};

SingleIntegerRangeVariable* getVariable(const std::string& name) {
  return SingleIntegerRangeVariable::get(new std::string(name));  
}

////////////////////////////////////////////////////////////////////

// E + E
struct SingleIntegerRangeAddition : public SingleIntegerRangeExpr {
  SingleIntegerRangeExpr* l;
  SingleIntegerRangeExpr* r;
  
  SingleIntegerRangeAddition(SingleIntegerRangeExpr* l,
                             SingleIntegerRangeExpr* r) : l(l), r(r) {}
  virtual raw_ostream& dump(raw_ostream& out) const {
    return out << "( " << l << " + " << r << " )";
  }
  virtual SingleIntegerRange* evaluate(Valuation* p) {
    SingleIntegerRange* rl = l->evaluate(p);
    SingleIntegerRange* rr = r->evaluate(p);
    return SingleIntegerRange::get(rl->lo + rr->lo,
                                   rl->hi + rr->hi);
  }
  
  virtual SingleIntegerRangeExpr* negate() {
    return plus(l->negate(), r->negate());
  }
  
  virtual void variablesUsed(std::set<SingleIntegerRangeVariable*>& vars) {
    l->variablesUsed(vars);
    r->variablesUsed(vars);
  }
};

////////////////////////////////////////////////////////////////////

// n * X
struct SingleIntegerRangeScalarMult : public SingleIntegerRangeExpr {
  SingleIntegerRangeVariable* x;
  llvm::APInt n; // can't be +-inf
  
  SingleIntegerRangeScalarMult(SingleIntegerRangeVariable* x,
                               const llvm::APInt& n) : x(x), n(n) {}
                               
  virtual raw_ostream& dump(raw_ostream& out) const {
    return out << "( " << x << " * " << n << " )";
  }
  
  virtual SingleIntegerRange* evaluate(Valuation* p) {
    SingleIntegerRange* r = x->evaluate(p);
    IntOrInf nl = r->lo * n;
    IntOrInf nu = r->hi * n;
    return SingleIntegerRange::get(inf(nl, nu), sup(nl, nu));
  }
  
  virtual SingleIntegerRangeExpr* negate() {
    return mult(-n, x->getNegativeVersion());
  }
  
  virtual void variablesUsed(std::set<SingleIntegerRangeVariable*>& vars) {
    vars.insert(x);
  }
};

////////////////////////////////////////////////////////////////////

struct SingleIntegerRangeConstraint {
  SingleIntegerRangeExpr* e;
  // implied meet; if r = top = [-inf, +inf], it may be elided.
  SingleIntegerRange* r;
  
  // implied <=
  
  SingleIntegerRangeVariable* x;
  
  raw_ostream& dump(raw_ostream& out) const {
    out << (*e);
    if (r != SingleIntegerRange::getTop()) {
      out << " meet " << *r;
    }
    out << " <= " << *x;
    return out;
  }
  
  void addNonNegativeVersionsTo(std::vector<SingleIntegerRangeConstraint*>&);
};

SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                            SingleIntegerRange* r,
                                            SingleIntegerRangeVariable* x) {
  SingleIntegerRangeConstraint* c = new SingleIntegerRangeConstraint();
  c->e = e;
  c->r = r;
  c->x = x;
  return c;
}

SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                            SingleIntegerRangeVariable* x) {
  return getConstraint(e, SingleIntegerRange::getTop(), x);
}

////////////////////////////////////////////////////////////////////

bool operator<=(const SingleIntegerRange& x, const SingleIntegerRange& y) {
  if (x.isEmpty()) return true;
  if (y.isEmpty()) return false;
  
  // [l1, u1] <= [l2, u2] if l2 <= l1 <= u1 <= u2
  return (y.lo <= x.lo
               && x.lo <= x.hi
                       && x.hi <= y.hi);
}

const SingleIntegerRange* meet(const SingleIntegerRange* x, const SingleIntegerRange* y) {
  if (x->isEmpty()) return x;
  return SingleIntegerRange::get(sup(x->lo, y->lo), inf(x->hi, y->hi));
}

const SingleIntegerRange* join(const SingleIntegerRange* x, const SingleIntegerRange* y) {
  if (x->isEmpty()) return y;
  return SingleIntegerRange::get(inf(x->lo, y->lo), sup(x->hi, y->hi));
}

const SingleIntegerRange* computeMeet(const SingleIntegerRange* a, const SingleIntegerRange *b) {
  return meet(a, b);
}
const SingleIntegerRange* computeJoin(const SingleIntegerRange* a, const SingleIntegerRange *b) {
  return join(a, b);
}
  


SingleIntegerRangeVariable* // static 
SingleIntegerRangeVariable::get(const std::string* name) {
  static std::map<std::string, SingleIntegerRangeVariable*> uniq;
  static std::vector<std::string> gripper;
  
  SingleIntegerRangeVariable* v = uniq[*name];
  if (!v) {
    gripper.push_back(*name);
    v = new SingleIntegerRangeVariable(name);
    uniq[*name] = v;
  }
  return v;
}

llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRange& e) {
  return e.dump(out);
}
llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeConstraint& e) {
  return e.dump(out);
}
llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeVariable& e) {
  return e.dump(out);
}

////////////////////////////////////////////////////////////////////

SingleIntegerRangeExpr* expr(SingleIntegerRange* r) { return r; }
SingleIntegerRangeExpr* expr(SingleIntegerRangeVariable* r) { return r; }

SingleIntegerRangeExpr* plus(SingleIntegerRangeExpr* a,
                             SingleIntegerRangeExpr* b) {
  return new SingleIntegerRangeAddition(a, b);
}

SingleIntegerRangeExpr* mult(const llvm::APInt& n,
                             SingleIntegerRangeVariable* v) {
  return new SingleIntegerRangeScalarMult(v, n);
}
SingleIntegerRangeExpr* mult(const llvm::APInt* n,
                             SingleIntegerRangeVariable* v) {
  return mult(*n, v);
}

const llvm::APInt* getNewAPInt(int n) {
  return new llvm::APInt(sizeof(int)*4, n, true);
}

const llvm::APInt getAPInt(int n) {
  return llvm::APInt(sizeof(int)*4, n, true);
}

bool Valuation::satisfies(SingleIntegerRangeConstraint* c) {
  SingleIntegerRange* er = evaluate(c->e);
  SingleIntegerRange* ex = evaluate(c->x);
  return *meet(er, c->r) <= *ex;
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

struct SingleIntegerRangeConstraintSet::Impl {
  std::vector<SingleIntegerRangeConstraint*> constraints;
  Valuation rho;

  void transformToRemoveNegativeConstraints();
  void variablesUsed(std::set<SingleIntegerRangeVariable*>&);
};

SingleIntegerRangeConstraintSet::SingleIntegerRangeConstraintSet() {
  impl = new Impl();
}

void SingleIntegerRangeConstraintSet::insert(SingleIntegerRangeConstraint* c) {
  ASSERT(c != NULL);
  impl->constraints.push_back(c);
}

SingleIntegerRange* SingleIntegerRangeConstraintSet::solve() {
  impl->transformToRemoveNegativeConstraints();
  typedef std::set<SingleIntegerRangeVariable*>  VarSet;
  VarSet vars;
  impl->variablesUsed(vars);
  for (VarSet::iterator it = vars.begin(); it != vars.end(); ++it) {
    SingleIntegerRangeVariable* var = *it;
    //llvm::outs() << "var: " << *var << "\n";
    //impl->rho.p[var] = getConstantRange(1, 2);
  }
  return getTopRange();
}


void SingleIntegerRangeConstraintSet::Impl::transformToRemoveNegativeConstraints() {
 
  for (size_t i = 0; i < constraints.size(); ++i) {
    ASSERT(constraints[i] != NULL) << "constraint " << i << "/" << constraints.size() << " null??";
  }
  
  std::vector<SingleIntegerRangeConstraint*> initialConstraints(constraints);
  constraints.clear();

  for (size_t i = 0; i < initialConstraints.size(); ++i) {
    initialConstraints[i]->addNonNegativeVersionsTo(constraints);
  }
}

// [l, u] => [-u, -l]
SingleIntegerRange* inverse(SingleIntegerRange* r) {
  return SingleIntegerRange::get(-(r->hi), -(r->lo));
}

void SingleIntegerRangeConstraint::addNonNegativeVersionsTo(
      std::vector<SingleIntegerRangeConstraint*>& constraints) {
  ASSERT(this != NULL);
  bool replaced = false;
  
  // c == [l, u] /\ TOP  <=  X
  if (r == getTopRange() && x->isNeutral()) {
    if (SingleIntegerRange* er = dynamic_cast<SingleIntegerRange*>(e)) {
      constraints.push_back(getConstraint(er,          x->getPositiveVersion()));
      constraints.push_back(getConstraint(inverse(er), x->getNegativeVersion()));
      replaced = true;
    }
  }
  
  
  SingleIntegerRangeVariable* Y = x;
  
  if (SingleIntegerRangeAddition* add = dynamic_cast<SingleIntegerRangeAddition*>(e)) {
    if (SingleIntegerRangeScalarMult* m = dynamic_cast<SingleIntegerRangeScalarMult*>(add->l)) {
      const llvm::APInt& a = m->n;
      SingleIntegerRangeVariable* X = m->x;
      SingleIntegerRangeExpr* b = add->r;

      if (X->isNeutral()) {
        replaced = true;
        if (a.isNegative()) {
          // c == (aX + b) /\ [l,u]  <= Y  (a < 0)
          //
          // ==:>
          //      (-a X- +  b) /\ [ l,  u] <= Y+
          //      (-a X+ + -b) /\ [-u, -l] <= Y-
          constraints.push_back(getConstraint(
            plus(mult(-a, X->getNegativeVersion()), b),
                                                r,  Y->getPositiveVersion()));
          
          constraints.push_back(getConstraint(
            plus(mult(-a, X->getPositiveVersion()), b->negate()),
                                        inverse(r), Y->getNegativeVersion()));
        } else {
          // c == (aX + b) /\ [l,u]  <= Y  (a > 0)
          //
          // ==:>
          //      ( a X+ +  b) /\ [ l,  u] <= Y+
          //      ( a X- + -b) /\ [-u, -l] <= Y-
          constraints.push_back(getConstraint(
            plus(mult( a, X->getPositiveVersion()), b),
                                                r,  Y->getPositiveVersion()));
          
          constraints.push_back(getConstraint(
            plus(mult( a, X->getNegativeVersion()), b->negate()),
                                        inverse(r), Y->getNegativeVersion()));
        }
      }
    }
  }
  
  if (!replaced) {
    llvm::errs() << "Un-replaced constraint: " << *this << "\n";
  }
}

void SingleIntegerRangeConstraintSet::Impl::variablesUsed(
                               std::set<SingleIntegerRangeVariable*>& vars) {
  for (size_t i = 0; i < constraints.size(); ++i) {
    constraints[i]->e->variablesUsed(vars);
    vars.insert(constraints[i]->x);
  }
}

} // namespace foster
