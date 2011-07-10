// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

// Refresher: on x86, stack frames look like this,
// provided we've told LLVM to disable frame pointer elimination:
// 0x0
//      ........
//    |-----------|
//    |local vars | <- top of stack
//    |saved regs |
//    |   etc     |
//    |-----------|
// +--| prev ebp  | <-- %ebp
// |  |-----------|
// |  | ret addr  | (PUSHed by call insn)
// |  |-----------|
// |  | fn params |
// v  | ......... |
//
// 0x7f..ff (kernel starts at 0x80....)
//
// Each frame pointer stores the address of the previous
// frame pointer.
struct frameinfo { frameinfo* frameptr; void* retaddr; };

// obtain frame via (frameinfo*) __builtin_frame_address(0)
int foster_backtrace(frameinfo* frame, frameinfo* frames, size_t frames_sz) {
  int i = 0;
  while (frame && frames_sz --> 0) {
    if (1 && frame) {
      fprintf(gclog, "...... frame: %p, frameptr: %p, retaddr: %p\n", frame, frame->frameptr, frame->retaddr);
      fflush(gclog);
    }
    frames[i] = (*frame);
    frame     = (*frame).frameptr;
    ++i;
  }
  return i;
}

