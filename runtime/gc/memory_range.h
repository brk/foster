// Copyright (c) 2021 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_GC_MEMORY_RANGE
#define FOSTER_GC_MEMORY_RANGE

#include <inttypes.h>
#include <cstring> // for memset()
#include "gc_helpers.h" // for distance()

namespace foster {
namespace runtime {
namespace gc {

struct memory_range {
  void* base;
  void* bound;
  bool contains(void* addr) const { return base <= addr && addr < bound; }
  const char* rel(void* addr) const {
    if (addr <  base) return "before";
    if (addr >= bound) return "after";
    return "within";
  }
  size_t size() const { return distance(base, bound); }

  void wipe_memory(uint8_t byte) { memset(base, byte, size()); }
};

}
}
}

#endif // FOSTER_GC_MEMORY_RANGE

