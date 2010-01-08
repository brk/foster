// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef H_4b440d519a9368_91435229
#define H_4b440d519a9368_91435229

#include "FosterASTVisitor.h"

#include <string>
#include <deque>
#include <vector>
#include <sstream>
#include <cassert>

// TODO: one difficulty with the current design is that
// classes unilaterally choose whether to manually or automatically
// apply a visitor to their child nodes, but pretty printing should basically
// never be done bottom-up, I think? 

// Straightforward implementation of Oppen's prettyprinting algorithm from
// ftp://db.stanford.edu/pub/cstr/reports/cs/tr/79/770/CS-TR-79-770.pdf

struct PrettyPrintPass : public FosterASTVisitor {
  #include "FosterASTVisitor.decls.inc.h"
  
  virtual void visitChildren(ExprAST* ast) {} // Only visit children manually!
  
  struct PPToken {
    PPToken() : kind(kBlank), str(""), len(0), offset(2), isConsistent(true) {}
    explicit PPToken(const std::string& str, bool isConsistent = false, int offset = 2, int blankSpace = 1)
      : kind(kString), str(str), len(str.size()), offset(offset), blankSpace(blankSpace), isConsistent(isConsistent) {
      if (str == " " || str == "\n") {
        kind = kBlank;
        len = blankSpace;
      }
      if (str == "\n") len = 9999;
    }
    enum TokenKind { kString, kBlockOpen, kBlockClose, kBlank } kind;
    std::string str;
    int len, offset, blankSpace;
    bool isConsistent;
  };
  
  PPToken tBlockOpen;
  PPToken tBlockClose;
  
  // I believe this is correctly implemented for correctly-structured streams,
  // but the code seems to be fragile in its handling of malformed streams.
  PrettyPrintPass(std::ostream& out, int margin = 80) : out(out), margin(margin),
      spaceLeft(margin) {
    stream.resize(3 * margin);
    
    left = 0; right = 0;
    leftotal = 0; rightotal = 0;
    
    tBlockOpen.kind = PPToken::kBlockOpen;
    tBlockClose.kind = PPToken::kBlockClose;
  }
  
  // not virtual since I haven't put much thought into making this a good base
  ~PrettyPrintPass() {
    std::cerr << "~PrettyPrintPass" << std::endl;
    if (!S.empty()) {
      checkStack(0);
      advanceleft(stream[left]);
    }
    //indent(0);
  }
  
  std::stringstream ss;
  std::ostream& out;
  int margin;
  int spaceLeft;
  int left, right, leftotal, rightotal;
  
  int pop(std::deque<int>& S) { int rv = S.back(); S.pop_back(); return rv; }
  int popbottom(std::deque<int>& S) { int rv = S.front(); S.pop_front(); return rv; }
  
  void incrwrap(int& n) { n = (++n) % stream.size(); }
  
  enum { kFits, kConsistent, kInconsistent };
  std::deque<std::pair<int, int> > indentStack;
  
  std::string str(const std::deque<std::pair<int, int> >& x) {
    std::stringstream ss;
    for (int i = 0; i < x.size(); ++i) {
      if (i > 0) ss << ", ";
      ss << x[i].first;
    }
    return ss.str();
  }
  
  void emit(const PPToken& t) {
    //std::cerr << "Emit " << str(t.kind) << ": " << t.str << std::endl;
    if (t.kind == PPToken::kString) {
      if (t.len > spaceLeft) {
        //std::cerr << "Pretty printing error: line too long! String was '" << t.str << "'" << std::endl;
      }
      
      spaceLeft = std::max(0, spaceLeft - t.len);
      out << t.str;
    }
    if (t.kind == PPToken::kBlockOpen) {
      if (t.len > spaceLeft) {
        if (0) {
          std::cerr << "\t\tBlock open, Indent stack pushing " << spaceLeft << " - " << t.offset << std::endl;
          std::cerr << "\t\tindent stack is " << str(indentStack) << std::endl;
        }
        indentStack.push_back(std::make_pair(spaceLeft - t.offset, int(t.isConsistent ? kConsistent : kInconsistent)));
        
      } else {
        //std::cerr << "\t\t\tBlock open, Indent stack pushing (fits) " << 0 << std::endl;
        indentStack.push_back(std::make_pair(0, int(kFits)));
      }
    }
    if (t.kind == PPToken::kBlockClose) {
      std::pair<int, int> top = indentStack.back(); indentStack.pop_back();
      //std::cerr << "\t\tReplacing spaceLeft = " << spaceLeft << " with " << top.first << std::endl;
      spaceLeft = top.first;
    }
    if (t.kind == PPToken::kBlank) {
      std::pair<int, int> top = indentStack.back();
      if (top.second != kFits) {
        if (0) {
          std::cerr << "Emitting non-fitting blank, top.second: " << top.second << "; t.len = " << t.len << " >? " << spaceLeft 
                    << "; spaceLeft.. " << "(" << top.first << " - " << t.offset << ")" << " = " << (top.first - t.offset)
                    << "; indent = " << (margin - (top.first - t.offset)) << std::endl;
          out << "!" << std::endl << "!!";
        }
      }
      
      switch (top.second) {
      case kFits:
        spaceLeft -= t.blankSpace;
        indent(t.blankSpace);
        break;
        
      case kConsistent:
        spaceLeft = top.first - t.offset;
        printNewLine(margin - spaceLeft);
        out << "^";
        break;
        
      case kInconsistent:
        if (t.len > spaceLeft) {
          spaceLeft = top.first - t.offset;
          printNewLine(margin - spaceLeft);
          out << "$";
        } else {
          spaceLeft -= t.blankSpace;
          indent(t.blankSpace);
        }
        break;
      }
    }
  }
  
  void printNewLine(int n) { out << std::endl; indent(n); }
  void indent(int n) { out << string(n, '_'); }
  
  std::vector<PPToken> stream;
  std::deque<int> S;
  
  void advanceleft(const PPToken& t) {
    //std::cerr << "AdvanceLeft saw " << str(t.kind) << " token '" << t.str << "'" << " of len " << t.len << std::endl;
    if (t.len >= 0) {
      //std::cerr << "AdvanceLeft Emitting " << str(t.kind) << " = " << t.str << " ; " << t.len << std::endl;
      emit(t);
      if (t.kind == PPToken::kBlank) {
        leftotal += t.blankSpace;
      } else if (t.kind == PPToken::kString) {
        leftotal += t.len;
      }
      //std::cerr << "advanceleft " << left << " =? " << right << std::endl;
      if (left != right) {
        incrwrap(left);
        advanceleft(stream[left]);
      }
    }
  }
  
  std::string str(PPToken::TokenKind k) {
    if (k == PPToken::kBlockOpen) return "[";
    if (k == PPToken::kBlockClose) return "]";
    if (k == PPToken::kBlank) return "_";
    return "*";
  }
  
  void scan(PPToken t) {
    if (0) {
      ss << str(t.kind);
      std::cerr << "scan() saw total stream " << ss.str() << " : " << t.str << std::endl;
    }
    //std::cerr << "Saw token type " << str(t.kind) << " : " << t.str << " ; " << t.len << std::endl;
    
    int x = 0;
    if (t.kind == PPToken::kBlockOpen) {
      if (S.empty()) {
        leftotal = rightotal = 1;
        left = right = 0;
      } else {
        incrwrap(right);
      }
      t.len = -rightotal;
      stream[right] = t;
      //std::cerr << "Block open, len " << t.len << "; right = " << right << std::endl;
      S.push_back(right);
    } else
    if (t.kind == PPToken::kBlockClose) {
      if (S.empty()) {
        assert(t.len == 0);
        emit(t);
      } else {
        incrwrap(right);
        t.len = -1;
        stream[right] = t;
        S.push_back(right);  
      }
    } else
    if (t.kind == PPToken::kBlank) {
      if (S.empty()) {
        leftotal = rightotal = 1;
        left = right = 0;
      } else {
        incrwrap(right);
        checkStack(0);
        S.push_back(right);
        t.len = -rightotal;
        stream[right] = t;
        rightotal += t.blankSpace;
      }
    } else if (t.kind == PPToken::kString) {
      if (S.empty()) {
        emit(t);
      } else {
        incrwrap(right);
        t.len = t.str.size();
        stream[right] = t;
        rightotal += t.len;
        
        checkStream();
      }
    }
  }
  
  void checkStream() {
    if (rightotal - leftotal > spaceLeft) {
      if (!S.empty()) {
        if (left == S.front()) {
          stream[popbottom(S)].len = 9999;
        }
      }
      advanceleft(stream[left]);
      if (left != right) {
        checkStream();
      }
    }
  }
  
  void checkStack(int k) {
    if (S.empty()) return;
    
    const PPToken& t = stream[S.back()];
    if (t.kind == PPToken::kBlockOpen) {
      if (k > 0) {
        int x = pop(S);
        //std::cerr << "\t\t\tSetting stream["<<x<<"].len to " << "(" << t.len << "+"<<rightotal<<") = " << (t.len + rightotal) << std::endl;
        stream[x].len = t.len + rightotal;
        checkStack(k - 1);
      }
    } else if (t.kind == PPToken::kBlockClose) {
      stream[pop(S)].len = 1;
      checkStack(k + 1);
    } else {
      int x = pop(S);
      //std::cerr << "\t\t\tSetting stream["<<x<<"].len = " << (t.len + rightotal) << std::endl;
      stream[x].len = t.len + rightotal;
      if (k > 0) {
        checkStack(k);
      }
    }
  }
};

#endif // header guard
