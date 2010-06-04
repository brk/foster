#include <inttypes.h>
#include <cstdlib>
#include <cstdio>

#include "foster_gc.h"

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

void initialize() {

}

void cleanup() {

}

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta));

/////////////////////////////////////////////////////////////////

std::list<void*> allocated_blocks;

/////////////////////////////////////////////////////////////////

void gc();

static FILE* gclog = NULL;

void gcPrintVisitor(void** root, const void *meta) {
	fprintf(gclog, "root: %p -> %p, meta: %p\n", root, *root, meta);
}

int64_t heap_size = 0;
bool visited = false;

const int64_t MAX_HEAP_SIZE = 4 * 1024;

extern "C" void* memalloc(int64_t sz) {
	heap_size += sz;

	if (heap_size > MAX_HEAP_SIZE) {
		gc();
	}

	void* addr = malloc(sz);
	allocated_blocks.push_back(addr);
#if 0
	if (!gclog) {
		gclog = fopen("gclog.txt", "w");
	}

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

void sweep() {
	std::list<void*>::iterator iter;
	for (iter = allocated_blocks.begin();
	    iter != allocated_blocks.end(); /* ... */ ) {
		// advance iter before possibly erasing it
		std::list<void*>::iterator it = iter++;
		void* addr = *it;
		if (!mark_bitmap[addr]) {
			free(addr);
			allocated_blocks.erase(it);
			heap_size -= 32; // TODO get real block size
		}
	}
}

void gc() {
	mark();
	sweep();
	/*
	float heap_residency = float(heap_size) / float(MAX_HEAP_SIZE);
	printf("after gc, heap size is %lld/%lld = %f%% full\n",
			heap_size, MAX_HEAP_SIZE, heap_residency);
	*/
}

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

