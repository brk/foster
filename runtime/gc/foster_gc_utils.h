// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "foster_gc.h"

#include <inttypes.h>
#include <cstring> // for size_t

namespace foster {
namespace runtime {
namespace gc {

const unsigned int FOSTER_GC_DEFAULT_ALIGNMENT = 16;      // 0b0..010000
const unsigned int FOSTER_GC_DEFAULT_ALIGNMENT_MASK = 15; // 0b0..001111

// {{{ Pointer menagerie

// Macro from http://blog.nelhage.com/2010/10/using-haskells-newtype-in-c/
#define NEWTYPE(tag, repr)                  \
    typedef struct { repr val; } tag;       \
    static inline tag make_##tag(repr v) {  \
            return (tag){.val = v};         \
    }                                       \
    static inline repr tag##_val(tag v) {   \
            return v.val;                   \
    }

NEWTYPE(unchecked_ptr, tori*); // unchecked in the sense of "might be tagged".

template<typename T>
inline T mask_ptr(T p, uintptr_t mask) {
  return T(uintptr_t(p) & (~ mask));
}

inline tori* untag(unchecked_ptr p) {
  // Enum-like ctors are represented as small integers...
  return mask_ptr(unchecked_ptr_val(p), FOSTER_GC_DEFAULT_ALIGNMENT_MASK);
}

inline tori* tori_of_tidy(tidy* t) { return (tori*) t; }

// }}}

struct typemap;

// E.g. if powerOf2 is 4, performs the following mapping:
// 0 -> 0      1 -> 4
// 2 -> 4      3 -> 4
// 4 -> 4      5 -> 8
template <typename T>
inline T roundUpToNearestMultipleWeak(T v, uintptr_t powerOf2) {
  uintptr_t mask = powerOf2 - 1;
  return T((uintptr_t(v) + mask) & ~mask);
}

// Performs byte-wise addition on void pointer base
inline void* offset(void* base, intptr_t off) {
  return (void*) (((char*) base) + off);
}

template<typename T>
inline void incr_by(T* & base, intptr_t off) {
  base = (T*) offset((void*)base, off);
}

inline size_t distance(void* base, void* bound) {
  return (char*) bound - (char*) base;
}

inline bool low_bits_zero(uintptr_t val, uintptr_t n) {
  return val == ((val >> n) << n);
}

// 4-byte alignment required for typeinfo structs.
const uint64_t HEADER_MARK_BITS = 0x01; // 0b000..00001
const uint64_t FORWARDED_BIT    = 0x02; // 0b000..00010
const uint64_t ALL_HEADER_BITS = HEADER_MARK_BITS | FORWARDED_BIT;

// This should remain synchronized with getHeapCellHeaderTy()
// in Codegen-typemaps.cpp
#define HEAP_CELL_HEADER_TYPE uint64_t
#define HEAP_CELL_HEADER_SIZE (sizeof(HEAP_CELL_HEADER_TYPE))

struct heap_cell {
  HEAP_CELL_HEADER_TYPE header;
  unsigned char         body[0];
  //======================================
  tidy*   body_addr() { return reinterpret_cast<tidy*>(&body); }
  int64_t cell_size() { return header; }

  // Precondition: not forwarded
  const typemap* get_meta() {
    return reinterpret_cast<const typemap*>(get_unmarked_header());
  }

  void set_header(const typemap* data, uintptr_t mark_bits) { header = HEAP_CELL_HEADER_TYPE(data) | HEAP_CELL_HEADER_TYPE(mark_bits); }

  bool is_forwarded() { return (header & FORWARDED_BIT) != 0; }
  void set_forwarded_body(tidy* newbody) {
    header = HEAP_CELL_HEADER_TYPE(newbody) | FORWARDED_BIT;
  }
  tidy* get_forwarded_body() { return (tidy*) (header & ~FORWARDED_BIT); }
  uint8_t get_mark_bits() { return (header & HEADER_MARK_BITS); }
  void flip_mark_bits() { header = (header ^ HEADER_MARK_BITS); }
  uint64_t get_unmarked_header() { return header & ~HEADER_MARK_BITS; }
  void clear_mark_bits() { header = get_unmarked_header(); }

  static heap_cell* for_tidy(tidy* ptr) {
    return (heap_cell*) offset((void*)ptr, -(intptr_t(HEAP_CELL_HEADER_SIZE)));
  }
};

struct heap_array {
  HEAP_CELL_HEADER_TYPE header;
  int64_t               arsz;
  unsigned char         elts[0];
  //======================================
  tidy* body_addr() { return reinterpret_cast<tidy*>(&arsz); }
  intr* elt_body(int64_t cellnum, int64_t cellsz) {
    return (intr*) offset((void*)&elts, cellnum * cellsz);
    // TODO invariant which means cellnum * cellsz will not overflow?
  };
  int64_t num_elts() { return arsz; }
  void set_num_elts(int64_t n) { arsz = n; }


  bool is_forwarded() { return (header & FORWARDED_BIT) != 0; }
  void set_forwarded_body(tidy* newbody) {
    header = HEAP_CELL_HEADER_TYPE(newbody) | FORWARDED_BIT;
  }
  tidy* get_forwarded_body() { return (tidy*) (header & ~FORWARDED_BIT); }
  uint8_t get_mark_bits() { return (header & HEADER_MARK_BITS); }
  void flip_mark_bits() { header = (header ^ HEADER_MARK_BITS); }
  uint64_t get_unmarked_header() { return header & ~HEADER_MARK_BITS; }
  void clear_mark_bits() { header = get_unmarked_header(); }

  const typemap* get_meta() {
    return reinterpret_cast<const typemap*>(get_unmarked_header());
  }

  void set_header(const typemap* m, uintptr_t mark_bits) { header = HEAP_CELL_HEADER_TYPE(m) | HEAP_CELL_HEADER_TYPE(mark_bits); }

  static heap_array* from_heap_cell(heap_cell* ptr) {
    return reinterpret_cast<heap_array*>(ptr);
  }
};

template <typename T>
struct heap_handle {
  void* unaligned_malloc;
  HEAP_CELL_HEADER_TYPE header;
  T* body;
  uint8_t padding[16];

  heap_cell* as_cell() { return (heap_cell*) &header; }
  tidy     * as_tidy() { return (tidy*)      &body; }

  static heap_handle* for_tidy(tidy* ptr) {
    return (heap_handle*) offset((void*)ptr, -(intptr_t(sizeof(void*) + HEAP_CELL_HEADER_SIZE)));
  }
};


// This structure describes the layout of a particular type,
// giving offsets and type descriptors for the pointer slots.
// Note that the GC plugin emits unpadded elements!
struct typemap {
  int64_t     cell_size;
  const char* name;
  int32_t     numOffsets;
  int8_t      ctorId;
  int8_t      isCoro;
  int8_t      isArray;
  int8_t      unused_padding;
  int32_t     offsets[0];
};

struct stackmap {
  // A safe point is a location in the code stream where it is
  // safe for garbage collection to happen (that is, where the
  // code generator guarantees that any registers which might
  // hold references to live objects have been stored on the stack).
  //
  // A point cluster is a collection of safe points which share
  // the same layout of live pointers. Because LLVM does not (as of
  // this writing) calculate liveness information, all safe points
  // in the same function wind up with the same "live" variables.
  int32_t pointClusterCount;
  int32_t _padding;
  struct PointCluster {
    // register_stackmaps() assumes it knows the layout of this struct!
    int32_t frameSize;
    int32_t addressCount;
    int32_t liveCountWithMetadata;
    int32_t liveCountWithoutMetadata;
    void*   safePointAddresses[0];
    void*   metadata[0];
    int32_t liveOffsetsWithMetadata[0];
    int32_t liveOffsetsWithoutMetadata[0];
    // maybe one int32_t for padding...

    const void* const* getMetadataStart() const {
      return &((void**)safePointAddresses)[addressCount];
    }

    const int32_t* getLiveOffsetWithMetaStart() const {
      return (int32_t*) &(getMetadataStart())[liveCountWithMetadata];
    }

    const int32_t* getLiveOffsetWithoutMetaStart() const {
      return (int32_t*) &(getLiveOffsetWithMetaStart())[liveCountWithMetadata];
    }
  };
  PointCluster pointClusters[0];
};

struct stackmap_table {
  int32_t numStackMaps;
  stackmap stackmaps[0];
};

} } } // namespace foster::runtime::gc

// This symbol is emitted by the fostergc LLVM GC plugin to the
// final generated assembly.
extern "C" {
  extern foster::runtime::gc::stackmap_table foster__gcmaps;
}
