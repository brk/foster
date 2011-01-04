// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef LIBFOSTER_H
#define LIBFOSTER_H

#include <stdint.h>

// This file exists to provide symbols to link
// libfoster_main.cpp::main() to libfoster

namespace foster {
namespace runtime {

void initialize();
void cleanup();

template <typename T>
inline bool notstale(T* p) {
  return *((uintptr_t*) p) != ~0;
}


struct FosterClosurei32i32 {
  int32_t (*code)(void* env, int32_t);
  void* env;
};

} // namespace foster::runtime
} // namespace foster

//////////////////////////////////////////////////////////////////

extern "C" {

// Interface to foster's memory allocator; see gc/foster_gc_allocate.cpp
void* memalloc_cell(void* typeinfo);

}

#endif
