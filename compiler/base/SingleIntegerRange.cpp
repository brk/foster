// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/SingleIntegerRange.h"

#include <map>
#include <vector>

#include "llvm/ADT/APInt.h"
#include "llvm/Support/raw_ostream.h"

using llvm::raw_ostream;

namespace foster {
  
  struct SingleIntegerRangeVariable;
  
struct Valuation {
  std::map<SingleIntegerRangeVariable*, SingleIntegerRange*> p;
  
  virtual SingleIntegerRange* evaluate(SingleIntegerRangeExpr* e) {
    return e->evaluate(this);
  }
};

////////////////////////////////////////////////////////////////////

struct IntOrInf {
  int inf; // -1 = -inf, +1 = +inf, 0 = finite
  llvm::APInt n;
  
  IntOrInf(int inf, const llvm::APInt& n) : inf(inf), n(n) {}
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
  else { return IntOrInf(x.inf, x.n * n); }
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
    return out << "[" << lo << ", " << hi << "]";
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
    top = get(IntOrInf(-1, llvm::APInt(32, 1234567, true)),
              IntOrInf(+1, llvm::APInt(32, 1234567, true)));
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
    IntOrInf(0, llvm::APInt(32, x, true)),
    IntOrInf(0, llvm::APInt(32, y, true)));
}

SingleIntegerRange* getMinRange(int x) {
  return SingleIntegerRange::get(
    IntOrInf(0, llvm::APInt(32, x, true)),
    IntOrInf(+1, llvm::APInt(32, x, true)));
}

SingleIntegerRange* getMaxRange(int x) {
  return SingleIntegerRange::get(
    IntOrInf(-1, llvm::APInt(32, x, true)),
    IntOrInf(0, llvm::APInt(32, x, true)));
}

////////////////////////////////////////////////////////////////////

struct SingleIntegerRangeVariable : public SingleIntegerRangeExpr {
  const char* name;
  // Returns a unique pointer for each string
  static SingleIntegerRangeVariable* get(const std::string& name);
  
  virtual SingleIntegerRange* evaluate(Valuation* p) { return p->p[this]; }
  
  virtual raw_ostream& dump(raw_ostream& out) const {
    return out << name; 
  }
private:
  SingleIntegerRangeVariable(const char* name) : name(name) {}
};

SingleIntegerRangeVariable* getVariable(const std::string& name) {
  return SingleIntegerRangeVariable::get(name);  
}

////////////////////////////////////////////////////////////////////

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
};

////////////////////////////////////////////////////////////////////

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
};

SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                            SingleIntegerRange* r,
                                            const std::string& var) {
  SingleIntegerRangeConstraint* c = new SingleIntegerRangeConstraint();
  c->e = e;
  c->r = r;
  c->x = SingleIntegerRangeVariable::get(var);
  return c;
}

SingleIntegerRangeConstraint* getConstraint(SingleIntegerRangeExpr* e,
                                            const std::string& var) {
  return getConstraint(e, SingleIntegerRange::getTop(), var);
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





SingleIntegerRangeVariable* // static 
SingleIntegerRangeVariable::get(const std::string& name) {
  static std::map<std::string, SingleIntegerRangeVariable*> uniq;
  static std::vector<std::string> gripper;
  
  SingleIntegerRangeVariable* v = uniq[name];
  if (!v) {
    gripper.push_back(name);
    v = new SingleIntegerRangeVariable(gripper.back().c_str());
    uniq[name] = v;
  }
  return v;
}

SingleIntegerRangeExpr* expr(SingleIntegerRange* r) { return r; }

llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRange& e) {
  return e.dump(out);
}
llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeConstraint& e) {
  return e.dump(out);
}
llvm::raw_ostream& operator<<(llvm::raw_ostream& out, const SingleIntegerRangeVariable& e) {
  return e.dump(out);
}

} // namespace foster
