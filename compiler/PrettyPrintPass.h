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

// TODO: one difficulty with the current design is that
// classes unilaterally choose whether to manually or automatically
// apply a visitor to their child nodes, but pretty printing should basically
// never be done bottom-up, I think? 

// ftp://db.stanford.edu/pub/cstr/reports/cs/tr/79/770/CS-TR-79-770.pdf
struct PrettyPrintPass : public FosterASTVisitor {
  #include "FosterASTVisitor.decls.inc.h"
  
  virtual void visitChildren(ExprAST* ast) {} // Only visit children manually!
  
  struct PPToken {
    enum TokenKind { kString, kBlockOpen, kBlockClose, kBlank } kind;
    std::string str;
    int len;
  };
  
  PPToken tBlockOpen; 
  PPToken tBlockClose;
  
  PPToken PPToken_from(const std::string& str) {
    PPToken t = { (str == " ") ? PPToken::kBlank : PPToken::kString, str, str.size() };
    return t;
  }
  
  // A string is a PPStream
  // if s1..sk are streams, then kBlockOpen s1 kBlank ... kBlank sk kBlockClose is a stream
  
  // len kString = str.size()
  // len kBlank = 1 + len next block in stream
  // len kBlockOpen = len strings + num spaces until kBlockClose
  // len kBlockClose = 0
  
  // I believe this is correctly implemented for correctly-structured streams,
  // but the code seems to be fragile in its handling of malformed streams.
  PrettyPrintPass(std::ostream& out, int margin = 80) : out(out), margin(margin), spaceLeft(margin) {
    stream.resize(3 * margin);
    
    gExtraIndentation = 2;
    left = 0; right = 0;
    leftotal = 0; rightotal = 0;
    
    tBlockOpen.kind = PPToken::kBlockOpen; tBlockOpen.str = ""; tBlockOpen.len = 0;
    tBlockClose.kind = PPToken::kBlockClose; tBlockClose.str = ""; tBlockClose.len = 0;
  }
  
  std::stringstream ss;
  std::ostream& out;
  int gExtraIndentation;
  int margin;
  int spaceLeft;
  int left, right, leftotal, rightotal;
  
  int pop(std::deque<int>& S) { int rv = S.back(); S.pop_back(); return rv; }
  int popbottom(std::deque<int>& S) { int rv = S.front(); S.pop_front(); return rv; }
  
  void incrwrap(int& n) { n = (++n) % stream.size(); }
  
  std::deque<int> indentStack;
  std::string str(const std::deque<int>& x) {
    std::stringstream ss;
    for (int i = 0; i < x.size(); ++i) {
      if (i > 0) ss << ", ";
      ss << x[i];
    }
    return ss.str();
  }
  
  void emit(const PPToken& t) {
    if (t.kind == PPToken::kString) {
      spaceLeft -= t.len;
      out << t.str;
    }
    if (t.kind == PPToken::kBlockOpen) {
      //std::cerr << "Pushing back " << spaceLeft << std::endl;
      indentStack.push_back(spaceLeft);
    }
    if (t.kind == PPToken::kBlockClose) {
      spaceLeft = pop(indentStack);
    }
    if (t.kind == PPToken::kBlank) {
      bool nextBlockCanFitOnPresentLine = t.len <= spaceLeft;
      if (nextBlockCanFitOnPresentLine) {
        spaceLeft -= 1;
        out << " ";
      } else {
        spaceLeft = indentStack.back() - gExtraIndentation;
        int nspaces = std::max(0, margin - spaceLeft);
        std::cerr << "SpaceLeft = " << spaceLeft << "; " << nspaces <<std::endl;
        out << std::endl << string(nspaces, ' ');
      }
    }
  }
  
  std::vector<PPToken> stream;
  std::deque<int> S;
  
  void advanceleft(const PPToken& t) {
    if (t.len >= 0) {
      std::cerr << "AdvanceLeft Emitting " << str(t.kind) << " = " << t.str << " ; " << t.len << std::endl;
      emit(t);
      if (t.kind == PPToken::kBlank) {
        leftotal++;
      } else if (t.kind == PPToken::kString) {
        leftotal += t.len;
      }
      std::cerr << "advanceleft " << left << " =? " << right << std::endl;
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
    ss << str(t.kind);
    std::cerr << "scan() saw total stream " << ss.str() << " : " << t.str << std::endl;
    //std::cerr << "Saw token type " << str(t.kind) << " : " << t.str << " ; " << t.len << std::endl;
    
    int x = 0;
    if (t.kind == PPToken::kBlockOpen) {
      if (S.empty()) {
        left = right = leftotal = rightotal = 0;
      } else {
        incrwrap(right);
      }
      t.len = -rightotal;
      stream[right] = t;
      S.push_back(right);
    } else
    if (t.kind == PPToken::kBlockClose) {
      if (S.empty()) {
        emit(t);
      } else {
        incrwrap(right);
        t.len = 0;
        stream[right] = t;
       
        x = pop(S);
        stream[x].len += rightotal;
        if (stream[x].kind == PPToken::kBlank && !S.empty()) {
          x = pop(S);
          stream[x].len += rightotal;
        }
        if (S.empty()) {
          advanceleft(stream[left]);
        }
      }
    } else
    if (t.kind == PPToken::kBlank) {
      if (S.empty()) {
        left = right = rightotal = 0;
      } else {
        incrwrap(right);
        x = S.back();
        if (stream[x].kind == PPToken::kBlank) {
          stream[pop(S)].len = rightotal + stream[x].len;
        }
      }
      
      t.len = -rightotal;
      stream[right] = t;
      S.push_back(right);
      ++rightotal;
    } else if (t.kind == PPToken::kString) {
      if (S.empty()) {
        emit(t);
      } else {
        incrwrap(right);
        t.len = t.str.size();
        stream[right] = t;
        rightotal += t.len;
        while (rightotal - leftotal > spaceLeft) {
          stream[popbottom(S)].len = 999; // Force newline...
          advanceleft(stream[left]);
        }
      }
    }
  }
};

#endif // header guard
