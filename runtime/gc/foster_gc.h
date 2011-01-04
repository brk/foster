#include <inttypes.h>
#include <string>

namespace foster {
namespace runtime {
namespace gc {

void initialize();
void cleanup();
void force_gc_for_debugging_purposes();
std::string format_ref(void*);


// Performs byte-wise addition on void pointer base
inline void* offset(void* base, int off) {
  return (void*) (((char*) base) + off);
}

struct foster_typemap_2 {
  int64_t cell_size;
  const char* name;
  int32_t numPointers;
  struct entry {
    const void* typeinfo;
    int32_t offset;
  };
  entry entries[2];
};

extern foster_typemap_2 foster_coro_i32_i32_typemap;

const uint64_t FORWARDED_BIT = 0x02; // 0b000..00010
// This should remain synchronized with getHeapCellHeaderTy()
// in Codegen-typemaps.cpp
#define HEAP_CELL_HEADER_SIZE (sizeof(int64_t))

struct heap_cell {
  int64_t       size;
  unsigned char body[0];
  //======================================
  void* body_addr() { return (void*) &body; }
  int64_t cell_size() { return size; }
  void* get_meta() { return (void*) size; }

  void set_meta(void* meta) { size = (int64_t) meta; }
  void set_cell_size(int64_t sz) { size = sz; }

  bool is_forwarded() {
    return (((uint64_t) cell_size()) & FORWARDED_BIT) != 0;
  }
  void set_forwarded_body(void* newbody) {
    size = ((uint64_t) newbody) | FORWARDED_BIT;
  }
  void* get_forwarded_body() {
    return (void*) (((uint64_t) cell_size()) & ~FORWARDED_BIT);
  }

  static heap_cell* for_body(void* ptr) {
    return (heap_cell*) offset(ptr, -HEAP_CELL_HEADER_SIZE);
  }
};

/// @brief The map for a single function's stack frame. One of these is
///        compiled as constant data into the executable for each function.
///
/// Storage of metadata values is elided if the %metadata parameter to
/// @llvm.gcroot is null.
struct FrameMap {
  int32_t NumRoots;    //< Number of roots in stack frame.
  int32_t NumMeta;     //< Number of metadata entries. May be < NumRoots.
  const void *Meta[0]; //< Metadata for each root.
};

/// @brief A link in the dynamic shadow stack. One of these is embedded in the
///        stack frame of each function on the call stack.
struct StackEntry {
  StackEntry *Next;    //< Link to next stack entry (the caller's).
  const FrameMap *Map; //< Pointer to constant FrameMap.
  void *Roots[0];      //< Stack roots (in-place array).
};

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta));

} } } // namespace foster::runtime::gc
