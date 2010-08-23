// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PUGH_SINOFSKY_PRETTYPRINTER_H
#define FOSTER_PUGH_SINOFSKY_PRETTYPRINTER_H

#include "llvm/Support/raw_ostream.h"

#include <string>
#include <deque>
#include <vector>

namespace foster {

// Straightforward implementation of Pugh & Sinofsky's prettyprinting algorithm
// from    http://ecommons.library.cornell.edu/bitstream/1813/6648/1/87-808.pdf

struct PughSinofskyPrettyPrinter {
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
  
  llvm::raw_ostream& out;
  
  PPToken tBlockOpen, tBlockClose;
  PPToken tIndent, tDedent;
  PPToken tNewline, tOptNewline, tConnNewline;
  
  PughSinofskyPrettyPrinter(llvm::raw_ostream& out,
                            int width = 80,
                            int indent_width = 2)
      : out(out), INDENT_WIDTH(indent_width) {
    tBlockOpen.kind   = PPToken::kOpen;
    tBlockClose.kind  = PPToken::kClose;
    tIndent.kind      = PPToken::kIndent;
    tDedent.kind      = PPToken::kDedent;
    tNewline.kind     = PPToken::kNewline;
    tOptNewline.kind  = PPToken::kOptLinebreak;
    tConnNewline.kind = PPToken::kConnLinebreak;
    
    total_chars_enqueued = total_pchars_enqueued = 0;
    total_chars_flushed  = total_pchars_flushed = 0;
    current_level = break_level = overflowed_lines = 0;
    device_left_margin = 0; device_output_width = width;
    
    break_level = -1; // No groupings have yet been broken
  }
  
  ~PughSinofskyPrettyPrinter() {
    flush(); // whatever's left in the buffer
  }
  
  void flush() { print_buffer(buffer.size()); }
  
  
  const static short kInfinity = (1<<15) - 1;
  const int INDENT_WIDTH;
  int total_chars_enqueued, total_pchars_enqueued;
  int total_chars_flushed, total_pchars_flushed;
  int current_level, break_level; 
  int device_left_margin, device_output_width;
  int overflowed_lines;
                                                
  struct BufEntry {
    BufEntry(char c, PPToken::Kind k, short l) : character(c), kind(k), level(l) {}
    char  character;
    PPToken::Kind kind;
    short level;
  };
  
  struct BreakInfo {
    BreakInfo(int e, int l, bool c) : level(l), chars_enqueued(e), connected(c) {}
    int level;
    int chars_enqueued;
    bool  connected;
  };
  
  std::deque<BreakInfo> break_dq;
  std::deque<BufEntry>  buffer;
  
  void print_buffer(int k);
  void scan(PPToken t);
  void emit_newline();
};

#undef right_enqueue
#undef left_enqueue
#undef right_dequeue
#undef left_dequeue

} // namespace foster

#endif // header guard

