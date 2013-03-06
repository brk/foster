// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_OPERATOR_PRECEDENCE_H
#define FOSTER_OPERATOR_PRECEDENCE_H

#include <string>

namespace foster {

class OperatorPrecedenceTable {
public:
  OperatorPrecedenceTable();

  typedef std::string Operator;

  enum OperatorRelation {
    kNoRelationSpecified,
    kOpInvalidTogetherUnparenthesized,
    kOpBindsTighter,
    kOpBindsLooser
  };

  bool check();
  bool isKnownOperatorName(const std::string&);
  OperatorRelation get(const Operator& opa, const Operator& opb);

  void parseAsTighter(const Operator& a, const Operator& b);
  void parseAsLooser(const Operator& a, const Operator& b);

  void initWith(const OperatorPrecedenceTable& other);

private:
  struct Impl;
  Impl* impl;
  OperatorPrecedenceTable& operator=(const OperatorPrecedenceTable& other);
  OperatorPrecedenceTable(const OperatorPrecedenceTable& other);
};

} // namespace foster

#endif

