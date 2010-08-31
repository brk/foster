// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/Diagnostics.h"
#include "parse/OperatorPrecedence.h"

#include "pystring/pystring.h"

#include <vector>
#include <string>
#include <map>
#include <set>

#include <iostream>

// Rather than encode operator precedence into the ANTLR grammar,
// we use operator precedence parsing to build correct trees
// out of (effective) lists of binary operator usages.
//
// Rather than storing operator precedence as a single numerical
// precedence associated with each operator, thus forcing the
// precedence relation to be a total order, we explicitly
// store a separate value for each operator pair, allowing
// precedence to form a graph.
//
// This has a number of benefits. First and foremost, it allows input
// code to add new operators, with proper precedence information.
//
// Second, it allows precedence to be more declarative. After all,
// what the common names for precedence relations (left associative,
// right associative, higher precedence, non-associative, etc)
// boils down to is: for ops X and Y, what tree structure results
// from parsing  a X b  Y c     and      b Y c X a)?
//
// X tighter:   (a X b) Y c              b  Y (c X a)
//
// Equal prec,
// left assoc:  (a X b) Y c             (b  Y c) X a
//
// Equal prec,
// right assoc:  a X (b Y c)             b  Y (c X a)
//
//
// Lastly, building precedence tables at runtime opens the door
// to not only allowing modules to define operators for local use,
// but also for modules to import and export operator definitions, and
// for operator definitions to be locally scoped, like other bindings.

using namespace std;

namespace foster {

#if 0
OperatorPrecedenceTable::OperatorRelation inverse(OperatorRelation r) {
  switch (r) {
    case kNoRelationSpecified:              return r;
    case kOpInvalidTogetherUnparenthesized: return r;
    case kOpBindsTighter: return kOpBindsLooser;
    case kOpBindsLooser:  return kOpBindsTighter;
  }
}
#endif

struct OperatorPrecedenceTable::Impl {

  typedef pair<OperatorPrecedenceTable::Operator,
               OperatorPrecedenceTable::Operator> OpPair;

  typedef map<OpPair, OperatorRelation> OpTable;
  OpTable table;

  typedef set<string> OpSet;
  OpSet knownOperators;

  OperatorRelation get(const Operator& opa, const Operator& opb) {
    return table[ OpPair(opa, opb) ];
  }

  // returns true if table is complete
  bool check() {
    bool tableComplete = true;
    for (OpSet::iterator it = knownOperators.begin();
			 it != knownOperators.end(); ++it) {
      for (OpSet::iterator it2 = knownOperators.begin();
			   it2 != knownOperators.end(); ++it2) {
	OperatorRelation rel = table[ OpPair(*it, *it2) ];
	if (rel == kNoRelationSpecified) {
	  std::cout << "No relation specified between \t" << *it
		    << " and " << *it2 << std::endl;
	  tableComplete = false;
	}
      }
    }
    return tableComplete;
  }

  void parseAsTighter(const OperatorPrecedenceTable::Operator& a,
                      const OperatorPrecedenceTable::Operator& b) {
    table[ OpPair(a, b) ] = kOpBindsTighter;

    knownOperators.insert(a);
    knownOperators.insert(b);
  }

  void parseAsLooser(const OperatorPrecedenceTable::Operator& a,
                     const OperatorPrecedenceTable::Operator& b) {
    table[ OpPair(a, b) ] = kOpBindsLooser;

    knownOperators.insert(a);
    knownOperators.insert(b);
  }

  void parseAs(const string& a, const string& b) {
    // For now, we severely restrict the format of parseAs,
    // although I think it would not be tremendously difficult to
    // reuse the expression parser and compare tree structures
    // to infer precedences.

    vector<string> aparts;
    pystring::split(a, aparts);
    ASSERT(aparts.size() == 5)
       << "expected something like 'a o b o c': " << a;

    string opa = aparts[1];
    string opb = aparts[3];

    bool opaTighter = b[0] == '(';
    if (opaTighter) {
      parseAsTighter(opa, opb);
    } else {
      parseAsLooser(opa, opb);
    }
  }

  // Declares that the given ops are all equivalent in precedence.
  void equivPrec(const vector<string>& ops) {
    ASSERT(!ops.empty());
    const string& knownOp = ops[0];
    ASSERT(knownOperators.count(knownOp) == 1);

    // If op X has equivalent precedence to known op Y,
    // it means that for all Z, the table entry for
    // (X, Z) should be the same as exists for (Y, Z)
    // (and similarly for (Z, X) / (Z, Y)).

    // ..... known ops...Y.. |  new ops
    // .                 %   |%%%%%%%%
    // .                 %   |%%%%%%%%
    // .                 %   |%%%%%%%%
    // Y &&&&&&&&&&&&&&&&+&&&|++++++++
    // .                 %   |%%%%%%%%
    // .                 %   |%%%%%%%%
    // ----------------------+--------
    // new &&&&&&&&&&&&&&+&&&| filled in by
    // ops &&&&&&&&&&&&&&+&&&| leftAssoc/etc

    for (OpSet::iterator it = knownOperators.begin();
                         it != knownOperators.end(); ++it) {
      const OperatorPrecedenceTable::Operator& z = *it;
      for (vector<string>::const_iterator oit = ops.begin();
                                    oit != ops.end(); ++oit) {
	const string& x = *oit;
        table[ OpPair(x, z) ] = table[ OpPair(knownOp, z) ];
        table[ OpPair(z, x) ] = table[ OpPair(z, knownOp) ];
	knownOperators.insert(x);
      }
    }
  }

  void tighter(const string& tops, const string& lops) {
    vector<string> vtops;
    pystring::split(tops, vtops);

    vector<string> vlops;
    pystring::split(lops, vlops);

    for (int i = 0; i < vtops.size(); ++i) {
      for (int j = 0; j < vlops.size(); ++j) {
	const string& z = vtops[i];
	const string& q = vlops[j];
        // If Z binds tighter than Q,
        // parse   a Z b Q c   as (a Z b) Q c
        parseAsTighter(z, q);

        // parse   a Q b Z c   as a Q (b Z c)
        parseAsLooser(q, z);
      }
    }
  }

  // Declares that the ops in the given string are left-associative
  // with each other (and thus implicitly of the same precedence).
  //
  // Precondition: the first op in the string is known.
  void leftAssociativeSet(const string& ops) {
    vector<string> vops;
    pystring::split(ops, vops);
    for (size_t i = 0; i < vops.size(); ++i) {
      for (size_t j = 0; j < vops.size(); ++j) {
        parseAsTighter(vops[i], vops[j]);
      }
    }
    equivPrec(vops);
  }

  // Declares that all the ops in the given string
  // do not associate with each other (and are implicitly
  // of the same precedence).
  //
  // For example, passing "< <=" would make it an error to parse
  // a <= b < c (although (a <= b) < c would be accepted,
  // probably to later fail during typechecking).
  //
  // Precondition: the first op in the string is known.
  void nonAssociativeSet(const string& ops) {
    vector<string> vops;
    pystring::split(ops, vops);
    for (size_t i = 0; i < vops.size(); ++i) {
      for (size_t j = 0; j < vops.size(); ++j) {
	table[ OpPair(vops[i], vops[j]) ] = kOpInvalidTogetherUnparenthesized;
      }
    }
    equivPrec(vops);
  }

  // returns true if table is complete
  bool buildDefaultTable() {
    // * tighter than +
    parseAs("a + b * c", "a + (b * c)");
    parseAs("a * b + c", "(a * b) + c");

    // * tighter than <
    parseAs("a < b * c", "a < (b * c)");
    parseAs("a * b < c", "(a * b) < c");
    // Equivalent and more concise:
    tighter("+", "<");

    // < tighter than ==
    parseAs("a < b == c", "(a < b) == c");
    parseAs("a == b < c", "a == (b < c)");
    tighter("+ *", "==");

    // ==  tighter than and
    parseAs("a and b == c", "a and (b == c)");
    parseAs("a == b and c", "(a == b) and c");

    parseAs("a and b < c", "a and (b < c)");
    parseAs("a < b and c", "(a < b) and c");
    tighter("+ * == <", "and");

    // ** right associative
    //parseAs("a ** b ** c", "a ** (b ** c)");
    //tighter("**", "* + < and ==");

/*
    // k : v, k : v   === (k : v), (k : v)
    //tighter(":", ",");


    // k : v, k : a -> b   === (k : v), (k : (a -> b))
    //tighter("->", ":"); tighter(":", ",");


    // k : v, k : a, b -> c     =/=     (k : v), (k : ((a, b) -> c))
    //        because it implies a cyclic precedence relation:
    // bad: tighter("->", ":"); tighter(":", ","); tighter(",", "->");

    // Therefore
    // k : v, k : a, b -> c     ===     (k : v), (k : a), (b -> c)
    //tighter("->", ":"); tighter(":", ","); tighter("->", ",");
*/

    // a b + c == (a b) + c
    //tighter("juxtaposition", "+ * ** == < and");

    // e.g. (a + b + c) == ((a + b) + c)
    // and  (a b c)     == ((a b) c) 
    leftAssociativeSet("* /");
    leftAssociativeSet("+ -");
    leftAssociativeSet("and or");

    nonAssociativeSet("== !=");
    nonAssociativeSet("< <= > >=");

    return check();
  }

  const char* str(OperatorPrecedenceTable::OperatorRelation r) {
    switch (r) {
      case kNoRelationSpecified:              return "no relation";
      case kOpInvalidTogetherUnparenthesized: return "invalid";
      case kOpBindsTighter: return "tighter";
      case kOpBindsLooser:  return "looser";
    }
  }

  void dump() {
    for (OpSet::iterator it = knownOperators.begin();
			 it != knownOperators.end(); ++it) {
      for (OpSet::iterator it2 = knownOperators.begin();
			   it2 != knownOperators.end(); ++it2) {
        const char* relstr = str(table[ OpPair(*it, *it2) ]);
        std::cout << *it << "\t" << relstr << "\t" << *it2 << "\n";
      }
    }
  }
}; // OperatorPrecedenceTable::Impl

OperatorPrecedenceTable::OperatorPrecedenceTable() {
  impl = new Impl();
  impl->buildDefaultTable();
}

bool OperatorPrecedenceTable::check() {
  return impl->check();
}

OperatorPrecedenceTable::OperatorRelation
OperatorPrecedenceTable::get(const OperatorPrecedenceTable::Operator& opa,
                             const OperatorPrecedenceTable::Operator& opb) {
  return impl->get(opa, opb);
}

bool OperatorPrecedenceTable::isKnownOperatorName(const std::string& s) {
  return impl->knownOperators.count(s) == 1;
}

void OperatorPrecedenceTable::dump() {
  impl->dump();
}

} // namespace foster

