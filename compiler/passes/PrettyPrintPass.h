// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PASSES_PRETTYPRINT_PUGH
#define FOSTER_PASSES_PRETTYPRINT_PUGH

#include "parse/FosterASTVisitor.h"

#include <string>
#include <deque>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;

// Straightforward implementation of Pugh & Sinofsky's prettyprinting algorithm
// from    http://ecommons.library.cornell.edu/bitstream/1813/6648/1/87-808.pdf

// TODO opt linebreaks don't seem to be working as expected...
struct PrettyPrintPass : public FosterASTVisitor {
  #include "parse/FosterASTVisitor.decls.inc.h"
  
  virtual void visitChildren(ExprAST* ast) {
   // Only visit children manually!
  }
  
  struct PPToken {
    enum Kind { kString,
                kOpen, kClose,
                kIndent, kDedent,
                kNewline, kOptLinebreak, kConnLinebreak
    } kind;
    std::string str;
    
             PPToken()                       : kind(kOptLinebreak), str("") {}
    explicit PPToken(const std::string& str) : kind(kString),       str(str) {}
  };
  
  bool printVarTypes;
  PPToken tBlockOpen, tBlockClose;
  PPToken tIndent, tDedent;
  PPToken tNewline, tOptNewline, tConnNewline;
  
  PrettyPrintPass(std::ostream& out, int width = 80, int indent_width = 2)
    : printVarTypes(false), out(out), INDENT_WIDTH(indent_width) {
    tBlockOpen.kind = PPToken::kOpen;
    tBlockClose.kind = PPToken::kClose;
    tIndent.kind = PPToken::kIndent;
    tDedent.kind = PPToken::kDedent;
    tNewline.kind = PPToken::kNewline;
    tOptNewline.kind = PPToken::kOptLinebreak;
    tConnNewline.kind = PPToken::kConnLinebreak;
    
    total_chars_enqueued = total_pchars_enqueued = 0;
    total_chars_flushed  = total_pchars_flushed = 0;
    current_level = break_level = 0;
    device_left_margin = 0; device_output_width = width;
    
    break_level = -1; // No groupings have yet been broken
  }
  
  ~PrettyPrintPass() {
    flush(); // whatever's left in the buffer
  }
  void flush() { print_buffer(buffer.size()); }
  
  std::ostream& out;
  const static short kInfinity = (1<<15) - 1;
  const int INDENT_WIDTH;
  int total_chars_enqueued, total_pchars_enqueued;
  int total_chars_flushed, total_pchars_flushed;
  int current_level, break_level; 
  int device_left_margin, device_output_width;
                                                
  struct BufEntry {
    BufEntry(char c, PPToken::Kind k, short l) : character(c), kind(k), level(l) {}
    char  character;
    PPToken::Kind kind;
    short level;
  };
  
  struct BreakInfo {
    BreakInfo(int l, int e, bool c) : level(l), chars_enqueued(e), connected(c) {}
    int level;
    int chars_enqueued;
    bool  connected;
  };
  
  std::deque<BreakInfo> break_dq;
  std::deque<BufEntry>  buffer;
  
  void print_buffer(int k) {
    for (int i = 0; i < k; ++i) {
      BufEntry temp = buffer.front(); buffer.pop_front();
      total_chars_flushed += 1;
      switch (temp.kind) {
        case PPToken::kConnLinebreak:
          if (temp.level <= break_level) { out << std::endl << string(device_left_margin, ' '); } break;
        case PPToken::kNewline:            out << std::endl << string(device_left_margin, ' '); break;
        case PPToken::kIndent: device_left_margin += INDENT_WIDTH; break;
        case PPToken::kDedent: device_left_margin -= INDENT_WIDTH; break;
        default:
          total_pchars_flushed += 1;
          out << temp.character;
          break;
      }
    }
  }
    
  // left = front, right = back
  void scan(PPToken t) {
    switch (t.kind) {
    case PPToken::kString:
      for (size_t i = 0; i < t.str.size(); ++i) {
        char c = t.str[i];
        if (c == '\n') { // Handle explicit newline embedded in string
          break_dq.clear();
          break_level = current_level;
          buffer.push_back(BufEntry(c, PPToken::kNewline, kInfinity)); total_chars_enqueued += 1;
          print_buffer(buffer.size());
          continue;
        }
        
        if ((total_pchars_enqueued - total_pchars_flushed) + device_left_margin
          >= device_output_width) { // must split line
          if (!break_dq.empty()) { // split line at a break
            BreakInfo temp = break_dq.back(); break_dq.pop_back();
            break_level = temp.level;
            print_buffer(temp.chars_enqueued - total_chars_flushed);
            if (!temp.connected) {
              out << std::endl;
            }
            break_level = std::min(break_level, current_level);
          } else {
            //std::cerr << "No breaks to take!" << std::endl;
          }
        }
        
        buffer.push_back(BufEntry(t.str[i], t.kind, kInfinity));
        total_chars_enqueued += 1;
        total_pchars_enqueued += 1;
      }
      break;
    case PPToken::kOpen:  current_level++; break;
    case PPToken::kClose: current_level--; break;
    case PPToken::kIndent: buffer.push_back(BufEntry('>', t.kind, kInfinity)); total_chars_enqueued += 1; break;
    case PPToken::kDedent: buffer.push_back(BufEntry('<', t.kind, kInfinity)); total_chars_enqueued += 1; break;
    case PPToken::kNewline:
      break_dq.clear();
      break_level = current_level;
      buffer.push_back(BufEntry('\n', t.kind, kInfinity)); total_chars_enqueued += 1;
      print_buffer(buffer.size());
      break;
    case PPToken::kOptLinebreak:
      while (!break_dq.empty() && ( break_dq.front().level >  current_level
                                || (break_dq.front().level == current_level
                                 && !break_dq.back().connected))) {
        // discard breaks we are no longer interested in
        break_dq.pop_front();
      }
      
      break_dq.push_front(BreakInfo(total_chars_enqueued, current_level, false));
      break;
    case PPToken::kConnLinebreak:
      if (break_level < current_level) {
        while (!break_dq.empty() && break_dq.front().level >= current_level) {
          // discard breaks we're not interested in
          break_dq.pop_front();
        }
        buffer.push_back(BufEntry('\n', t.kind, current_level));
        total_chars_enqueued += 1;
        break_dq.push_front(BreakInfo(total_chars_enqueued, current_level, true));
      } else {
        break_dq.clear();
        buffer.push_back(BufEntry('\n', PPToken::kNewline, kInfinity));
        total_chars_enqueued += 1;
        print_buffer(buffer.size());
      }
      break;
    } // end switch
  }
};

#endif // header guard

