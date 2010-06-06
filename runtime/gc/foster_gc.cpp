#include <inttypes.h>
#include <cstdlib>
#include <cstdio>
#include <cstring>

#include "foster_gc.h"

#include "base/time.h"

namespace {
// This goes in a private namespace so that the symbol won't be
// exported in the bitcode file, which could interfere with llc
foster::runtime::gc::StackEntry *llvm_gc_root_chain;
}

/////////////////////////////////////////////////////////////////

// This implements a mark-sweep heap by doing the
// Simplest Thing That Could Possibly Work:
//
// We keep an explicit list of every allocation made, in order
// to make the sweep phase as simple as possible. The mark phase
// is simplified by storing mark bits in a STL map.
//
// This is, needless to say, hilariously inefficient, but it
// provides a baseline to measure improvements from.

#include <list>
#include <map>

namespace foster {
namespace runtime {
namespace gc {

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta));

FILE* gclog = NULL;

class copying_gc {
  class semispace {
	  semispace(uint64_t size) {
		  start = (char*) malloc(size);
		  end   = start + size;
		  bump  = start;
	  }

	  ~semispace() {
		free(start);
	  }

	  char* start;
	  char* end;
	  char* bump;

  public:
	  bool can_allocate(uint64_t size) {
        return bump + size < end;
	  }

	  void* allocate_prechecked(uint64_t size) {
		void* allot = bump;
		bump += size;
		((uint64_t*) allot)[0] = size;
		return &((uint64_t*) allot)[1];
	  }
  };

  semispace* curr;
  semispace* next;

  int num_allocations;
  int num_collections;

  void gc();

  // precondition: all active cells from curr have been copied to next
  void flip() {
	// curr is the old semispace, so we reset its bump ptr
	curr->bump = curr->start;
	std::swap(curr, next);
  }

public:
  copying_gc(uint64_t size) {
	curr = new semispace(size);
	next = new semispace(size);

	num_allocations = 0;
	num_collections = 0;
  }

  ~copying_gc() {
	fprintf(gclog, "num allocations: %d, num collections: %d\n",
			num_allocations, num_collections);
  }

  // copy the cell at the given address to the next semispace
  void copy(void* cell);

  void* allocate(uint64_t size) {
	++num_allocations;

	if (curr->can_allocate(size)) {
	  return curr->allocate_prechecked(size);
	} else {
	  gc();
	  if (curr->can_allocate(size)) {
		return curr->allocate_prechecked(size);
	  } else {
		return NULL;
	  }
	}
  }
};

copying_gc* allocator = NULL;

void copying_gc_root_visitor(void **root, const void *meta) {
  void* cell = *root;
  allocator->copy(cell);
}

void copying_gc::copy(void* cell) {
  uint64_t size = ((uint64_t*) cell)[0];
  memcpy(next->bump, cell, size);
  next->bump += size;
}

void copying_gc::gc() {
  ++num_collections;
  // copy all used blocks to the next semispace
  visitGCRoots(copying_gc_root_visitor);
  flip();
}

base::TimeTicks start;

void initialize() {
  gclog = fopen("gclog.txt", "w");

  const int KB = 1024;
  allocator = new copying_gc(32 * KB);

  start = base::TimeTicks::HighResNow();
}

void cleanup() {
  base::TimeDelta elapsed = base::TimeTicks::HighResNow() - start;
  fprintf(gclog, "Elapsed runtime: %lld.%lld s\n",
		  elapsed.InSeconds(), elapsed.InMilliseconds() - (elapsed.InSeconds() * 1000));

  delete allocator;
}

extern "C" void* memalloc(int64_t sz) {
	return allocator->allocate(sz);
}

#if 0
/////////////////////////////////////////////////////////////////

std::list<void*> allocated_blocks;

/////////////////////////////////////////////////////////////////

void mark();
void* lazy_sweep();

void gcPrintVisitor(void** root, const void *meta) {
	fprintf(gclog, "root: %p -> %p, meta: %p\n", root, *root, meta);
}

int64_t heap_size = 0;
bool visited = false;
bool marked = false;
int lazy_sweep_remaining = 0;
const int64_t MAX_HEAP_SIZE = 4 * 1024;

extern "C" void* memalloc_lazy_sweep(int64_t sz) {
	if (heap_size + sz > MAX_HEAP_SIZE) {
		if (!marked) { mark(); marked = true; lazy_sweep_remaining = allocated_blocks.size(); }
		void* addr = lazy_sweep();
		if (addr) return addr;
	}

	heap_size += sz;
	void* addr = malloc(sz);
	allocated_blocks.push_back(addr);
#if 0
	if (memalloc_call_num % 10 == 0) {
		fprintf(gclog, "after %lld calls, sz = +%lld, memalloced size: %lld\n",
			memalloc_call_num, sz, memalloced_size);
		fprintf(gclog, "have %d blocks; allocated block at address: %p\n",
			allocated_blocks.size(), addr);
		visitGCRoots(gcPrintVisitor);
	}
#endif
	return addr;
}

/////////////////////////////////////////////////////////////////

std::map<void*, bool> mark_bitmap;

// root is the stack address; *root is the heap address
void gcMarkingVisitor(void** root, const void *meta) {
	//printf("MARKING root: %p -> %p, meta: %p\n", root, *root, meta);
	// for now, we assume all allocations are atomic
	mark_bitmap[*root] = true;
}

void mark() {
	mark_bitmap.clear();
	visitGCRoots(gcMarkingVisitor);
}

void* lazy_sweep() {
	std::list<void*>::iterator iter;
	for (iter = allocated_blocks.begin();
	    iter != allocated_blocks.end() && --lazy_sweep_remaining >= 0; /* ... */ ) {
		// advance iter before possibly erasing it
		std::list<void*>::iterator it = iter++;
		void* addr = *it;
		if (!mark_bitmap[addr]) {
			// move reused block to the end of the list
			mark_bitmap[addr] = true;
			allocated_blocks.splice(allocated_blocks.end(), allocated_blocks, it);
			return addr;
		}
	}

	mark_bitmap.clear();
	marked = false;
	return NULL;
}
#endif
/////////////////////////////////////////////////////////////////

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta)) {
  for (StackEntry *R = llvm_gc_root_chain; R; R = R->Next) {
    unsigned i = 0;
    
    // For roots [0, NumMeta), the metadata pointer is in the FrameMap.
    for (unsigned e = R->Map->NumMeta; i != e; ++i)
      Visitor(&R->Roots[i], R->Map->Meta[i]);
    
    // For roots [NumMeta, NumRoots), the metadata pointer is null.
    for (unsigned e = R->Map->NumRoots; i != e; ++i)
      Visitor(&R->Roots[i], NULL);
  }
}

} } } // namespace foster::runtime::gc

