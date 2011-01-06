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

} } } // namespace foster::runtime::gc
