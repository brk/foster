// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/PughSinofskyPrettyPrinter.h"

#include "gtest/gtest.h"

#include <sstream>
#include <iostream>

using std::string;

namespace {

typedef foster::PughSinofskyPrettyPrinter PrettyPrinter;
typedef PrettyPrinter::PPToken PPToken;

// Simple single-pass scanner to implement the mini-language
// from the Pugh & Sinofsky paper:
//    _t    indent
//    _{    block open
//    _}    block close
//    _n    unconditional line break
//    _o    optional conditional line break (aka inconsistent)
//    _c    connected conditional line break (aka consistent)
void parse(PrettyPrinter& pp, const std::string& s) {
  size_t e = s.size();
  size_t i = 0;
  while (i < e) {
    // Collect span of non-control chars
    size_t b = i;
    while((i < e) && (s[i] != '_')) {
      ++i;
    }
    
    if (b < i) {
      pp.scan(PPToken(s.substr(b, i - b)));
    }
    
    // now, i == e or s[i] == "_"
    if (i != e) { //  s[i] == "_"
      if (++i < e) { // make sure string doesn't end with _
        switch (s[i]) {
          case 't': pp.scan(pp.tIndent); break;
          case 'b': pp.scan(pp.tDedent); break;
          case '{': pp.scan(pp.tBlockOpen); break;
          case '}': pp.scan(pp.tBlockClose); break;
          case 'n': pp.scan(pp.tNewline); break;
          case 'o': pp.scan(pp.tOptNewline); break;
          case 'c': pp.scan(pp.tConnNewline); break;
        }
        ++i;
      }
    }
  }
}


TEST(PughSinofskyPrettyPrinter, optNewlines) {
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 15, 2);
    parse(pp, "1234_o1234");
    }
    EXPECT_EQ("12341234", ss.str());
  }
  
  
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 7, 2);
    parse(pp, "1234_o1234");
    }
    EXPECT_EQ("1234\n1234", ss.str());
  }
}

TEST(PughSinofskyPrettyPrinter, simpleParsingGroupingNoBreaks) {
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 25, 2);
    parse(pp, "_t_{if _t_{x _o< 0_}_b then _o_{x _o:= -x_}_b_}_b");
    }
    EXPECT_EQ("if x < 0 then x := -x", ss.str());
  }
  
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 15, 2);
    parse(pp, "_t_{if _t_{x _o< 0_}_b then _o_{x _o:= -x_}_b_}_b");
    }
    EXPECT_EQ("if x < 0 then \n"
              "  x := -x", ss.str());
  }
}




TEST(PughSinofskyPrettyPrinter, singleTokenBasic) {
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 40, 2);
    pp.scan(PPToken("1234"));
    }
    EXPECT_EQ("1234", ss.str());
  }
}

// tNewline produces hard linebreak that would otherwise not appear.
TEST(PughSinofskyPrettyPrinter, reqNewlines) {
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 15, 2);
    parse(pp, "1234_n1234");
    }
    EXPECT_EQ("1234\n"
              "1234", ss.str());
  }
}

// tNewline produces hard linebreak that would otherwise not appear.
TEST(PughSinofskyPrettyPrinter, indentDedent) {
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 15, 2);
    // Indentation markers don't take effect until the next line,
    // so 1 does not get indented.
    parse(pp, "_n0_n_t1_b_n");
    }
    EXPECT_EQ("\n"
              "0\n"
              "1\n", ss.str());
  }
  
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 15, 2);
    // The _n after the _t inserts indentation spaces.
    parse(pp, "_n0_n_t1_n2_b_n");
    }
    EXPECT_EQ("\n"
              "0\n"
              "1\n"
              "  2\n", ss.str());
  }
  
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 15, 2);
    // Additional _ns without _ts maintain the same indentation level.
    parse(pp, "_n0_n_t1_n2_n3_b_n");
    }
    EXPECT_EQ("\n"
              "0\n"
              "1\n"
              "  2\n"
              "  3\n", ss.str());
  }
  
  {
    std::stringstream ss;
    {
    PrettyPrinter pp(ss, 15, 2);
    // Nesting works pretty much as expected.
    parse(pp, "_n"
              "0_n"
              "_t1_n"
                "2_n"
                "3_t_n"
                  "4_b_n"
                "5_b_n"
              "6_n"
              "7_n");
    }
    EXPECT_EQ("\n"
              "0\n"
              "1\n"
              "  2\n"
              "  3\n"
              "    4\n"
              "  5\n"
              "6\n"
              "7\n"
              , ss.str());
  }
}

} // unnamed namespace

