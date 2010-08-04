// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "passes/PughSinofskyPrettyPrinter.h"

// Straightforward implementation of Pugh & Sinofsky's prettyprinting algorithm
// from    http://ecommons.library.cornell.edu/bitstream/1813/6648/1/87-808.pdf

// left = front, right = back
#define right_enqueue push_back
#define left_enqueue push_front
#define right_dequeue pop_back
#define left_dequeue pop_front

typedef foster::PughSinofskyPrettyPrinter PrettyPrinter;
typedef PrettyPrinter::PPToken PPToken;

#if 0
void dump(PrettyPrinter* pp, std::string msg) {
  return;
  std::cerr << msg
    << "; current_level = " << pp->current_level
    << "; break_level = " << pp->break_level
    << "; chars_nqd = " << pp->total_chars_enqueued 
    << "; pchars_nqd = " << pp->total_pchars_enqueued
    << "; chars_flushed = " << pp->total_chars_flushed 
    << "; pchars_flushed = " << pp->total_pchars_flushed 
    << "; break_level = " << pp->break_level
    << "; left_margin = " << pp->device_left_margin
    << "; break_dq.size() = " << pp->break_dq.size()
    ;
    
   std::cerr << "\n";
}
#endif

void PrettyPrinter::scan(PPToken t) {
  switch (t.kind) {
  case PPToken::kOpen:  current_level++; break;
  case PPToken::kClose: current_level--; break_level = (std::min)(break_level, current_level); break;
  case PPToken::kIndent: buffer.right_enqueue(BufEntry('>', t.kind, kInfinity)); total_chars_enqueued += 1; break;
  case PPToken::kDedent: buffer.right_enqueue(BufEntry('<', t.kind, kInfinity)); total_chars_enqueued += 1; break;
  
  case PPToken::kNewline: // unconditional line break
    break_dq.clear();
    break_level = current_level;
    buffer.right_enqueue(BufEntry('\n', t.kind, kInfinity)); total_chars_enqueued += 1;
    print_buffer(buffer.size());
    break;

  case PPToken::kOptLinebreak: // optional line break
    while (!break_dq.empty() && ( break_dq.front().level >  current_level
                              || (break_dq.front().level == current_level
                               && !break_dq.back().connected))) {
      // discard breaks we are no longer interested in
      break_dq.left_dequeue();
    }
    
    break_dq.left_enqueue(BreakInfo(total_chars_enqueued, current_level, false));
    break;

  case PPToken::kConnLinebreak: // connected line break
    if (break_level < current_level) {
      while ((!break_dq.empty()) && break_dq.front().level >= current_level) {
        // discard breaks we're not interested in
        break_dq.left_dequeue();
      }
      buffer.right_enqueue(BufEntry('\n', t.kind, current_level));
      total_chars_enqueued += 1;
      break_dq.left_enqueue(BreakInfo(total_chars_enqueued, current_level, true));
    } else { // take an immediate line break, break level = current level
      break_dq.clear();
      buffer.right_enqueue(BufEntry('\n', PPToken::kNewline, kInfinity));
      total_chars_enqueued += 1;
      print_buffer(buffer.size());
    }
    break;
    
  case PPToken::kString:
    for (size_t i = 0; i < t.str.size(); ++i) {
      char c = t.str[i];
      if (c == '\n') { // Handle explicit newline embedded in string
        break_dq.clear();
        break_level = current_level;
        buffer.right_enqueue(BufEntry(c, PPToken::kNewline, kInfinity)); total_chars_enqueued += 1;
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
            emit_newline();
          }
          break_level = std::min(break_level, current_level);
        } else {
          //std::cerr << "No breaks to take!" << std::endl;
          overflowed_lines++;
        }
      }
      
      buffer.right_enqueue(BufEntry(t.str[i], t.kind, kInfinity));
      total_chars_enqueued += 1;
      total_pchars_enqueued += 1;
    }
    break;
  } // end switch
}

void foster::PughSinofskyPrettyPrinter::emit_newline() {
  out << '\n' << string(device_left_margin, ' ');
}

void foster::PughSinofskyPrettyPrinter::print_buffer(int k) {
  for (int i = 0; i < k; ++i) {
    BufEntry temp = buffer.front(); buffer.pop_front();
    total_chars_flushed += 1;
    switch (temp.kind) {
      case PPToken::kConnLinebreak:
        if (temp.level <= break_level) { emit_newline(); }       break;
      case PPToken::kNewline:            emit_newline();         break;
      case PPToken::kIndent: device_left_margin += INDENT_WIDTH; break;
      case PPToken::kDedent: device_left_margin -= INDENT_WIDTH; break;
      default:
        total_pchars_flushed += 1;
        out << temp.character;
        break;
    }
  }
}

#undef right_enqueue
#undef left_enqueue
#undef right_dequeue
#undef left_dequeue

