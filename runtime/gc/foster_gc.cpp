// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <inttypes.h>
#include <cstdlib>
#include <cstdio>
#include <cstring>

#include "foster_gc.h"
#include "FosterConfig.h"

#include "base/time.h"

#if USE_FOSTER_GC_PLUGIN
#include "execinfo.h"
#endif

/////////////////////////////////////////////////////////////////

#include <sstream>
#include <list>
#include <vector>
#include <map>

namespace foster {
namespace runtime {
namespace gc {

struct typemap {
  const char* name;
  int32_t numPointers;
  struct entry { const void* typeinfo; int32_t offset; };
  entry entries[0];
};

#if USE_FOSTER_GC_PLUGIN
struct stackmap {
  struct OffsetWithMetadata { void* metadata; int32_t offset; };

  int32_t pointClusterCount;
  struct PointCluster {
    int32_t frameSize;
    int32_t addressCount;
    int32_t liveCountWithMetadata;
    int32_t liveCountWithoutMetadata;
    OffsetWithMetadata
            liveOffsetsWithMetadata[0];
    int32_t liveOffsetsWithoutMetadata[0];
    void*   safePointAddresses[0];
  };
  PointCluster pointClusters[0];
};

struct stackmap_table {
  int32_t numStackMaps;
  stackmap stackmaps[0];
};

// This symbol is emitted by the fostergc LLVM GC plugin to the
// final generated assembly.
extern "C" stackmap_table __foster_gcmaps;
#endif

#define HEAP_CELL_FOR_BODY(ptr) ((heap_cell*) &((int64_t*)(ptr))[-1])
const uint64_t FORWARDED_BIT = 0x02;

struct heap_cell { int64_t _size; unsigned char _body[0];
  void* body() { return (void*) &_body; }
  int64_t size() { return _size; }
  void set_size(int64_t size) { _size = size; }

  bool is_forwarded() {
    return (((uint64_t) size()) & FORWARDED_BIT) != 0;
  }
  void set_forwarded_body(void* body) {
    _size = ((uint64_t) body) | FORWARDED_BIT;
  }
  void* get_forwarded_body() {
    return (void*) (((uint64_t) size()) & ~FORWARDED_BIT);
  }
};

// Performs byte-wise addition on void pointer base
void* offset(void* base, int off) {
  return (void*) (((char*) base) + off);
}

#if USE_FOSTER_GC_PLUGIN
void visitGCRootsWithStackMaps(void (*visitor)(void **root, const void *meta));
#else
void visitGCRoots(void (*visitor)(void **root, const void *meta));
#endif

FILE* gclog = NULL;

class copying_gc {
  class semispace {
	  semispace(int64_t size, copying_gc* parent) : parent(parent) {
		  start = (char*) malloc(size);
		  end   = start + size;
		  bump  = start;

		  genericClosureMarker = NULL;
	  }

	  ~semispace() {
		free(start);
	  }

	  char* start;
	  char* end;
	  char* bump;
	  copying_gc* parent;

	  char* genericClosureMarker;

  public:
	  bool contains(void* ptr) {
	    return (ptr >= start) && (ptr < end);
	  }

	  void clear() {
	    fprintf(gclog, "clearing mem from %p to %p\n", start, end);
	    memset(start, 255, end - start);
	  }

	  int64_t free_size() { return end - bump; }

	  bool can_allocate(int64_t size) {
        return bump + size < end;
	  }

	  void* allocate_prechecked(int64_t size) {
		heap_cell* allot = (heap_cell*) bump;
		bump += size;
		allot->set_size(size);
		return allot->body();
	  }

	  // Prerequisite: body is a stack pointer.
	  // Behavior:
	  // * Any slots containing stack pointers should be recursively update()ed.
	  // * Any slots containing heap pointers should be overwritten
	  // with copy()'d values.
	  void update(void* body, const void* meta) {
	    if (!meta) {
	      fprintf(gclog, "can't update body %p with no type map!\n", body);
	      return;
	    }

        const typemap* map = (const typemap*) meta;

        bool isClosure =
            (genericClosureMarker && genericClosureMarker == map->name)
            || strncmp("genericClosure", map->name, 14) == 0;
        if (isClosure) {

          // closure value is { code*, env = i8* }
          // but we don't want to use the (i8*) typemap entry for the env ptr.
          // Instead, we manually fetch the correct typemap from the
          // environment itself, and use it instead of e.typeinfo
          void** envptr_slot = (void**) offset(body, 4);
          void** envptr = *(void***) envptr_slot;
          if (!envptr) return;
          typemap* envmap = (typemap*) *envptr;
          if (this->parent->is_probable_stack_pointer(envptr, envptr_slot)) {
            update(envptr, envmap);
          } else {
            *envptr_slot = copy(envptr, envmap);
          }
          return;
        }

        // for each pointer field in the cell
        for (int i = 0; i < map->numPointers; ++i) {
          const typemap::entry& e = map->entries[i];
          void** oldslot = (void**) offset(body, e.offset);
#if 0
          fprintf(gclog, "update: body is %p, offset is %d, "
              "oldslot is %p, slotval is %p, typeinfo is %p\n",
              body, e.offset, oldslot, *oldslot, e.typeinfo);
#endif
          // recursively copy the field from cell, yielding subfwdaddr
          // set the copied cell field to subfwdaddr
          if (*oldslot != NULL) {
            if (this->parent->is_probable_stack_pointer(*oldslot, oldslot)) {
              update(*oldslot, e.typeinfo);
            } else {
              *oldslot = copy(*oldslot, e.typeinfo);
            }
          }
        }
	  }

	  // returns body of newly allocated cell
	  void* copy(void* body, const void* meta) {
	    if (!meta) {
	      void** bp4 = (void**)offset(body,4);
          fprintf(gclog, "called copy with null metadata\n");
          fprintf(gclog, "body   is %p -> %p\n", body, *(void**)body);
          fprintf(gclog, "body+4 is %p -> %p\n", offset(body,4), *bp4);
          fprintf(gclog, "body-4 is %p -> %p\n", offset(body,-4), *(void**)offset(body,-4));
          void** envptr = (void**)*bp4;
          fprintf(gclog, "envptr: %p -> %p\n", envptr, *envptr);
          typemap* envtm = (typemap*) *envptr;
          fprintf(gclog, "env tm name is %s, # ptrs = %d\n", envtm->name, envtm->numPointers);
          return NULL;
        }

	    heap_cell* cell = HEAP_CELL_FOR_BODY(body);

	    if (cell->is_forwarded()) {
	      void* fwd = cell->get_forwarded_body();
	      fprintf(gclog, "cell %p(->0x%x) considered forwarded to %p for body %p(->0x%x)\n",
	          cell, *(unsigned int*)cell, fwd, body, *(unsigned int*)body);
	      return fwd;
	    }

	    int64_t size = cell->size();

	    if (can_allocate(size)) {
	      memcpy(bump, cell, size);
	      heap_cell* new_addr = (heap_cell*) bump;
	      bump += size;

	      cell->set_forwarded_body(new_addr->body());

	      if (meta) {
	        const typemap* map = (const typemap*) meta;
	        // for each pointer field in the cell
	        for (int i = 0; i < map->numPointers; ++i) {
	          const typemap::entry& e = map->entries[i];
	          void** oldslot = (void**) offset(body, e.offset);

	          //fprintf(gclog, "body is %p, offset is %d, typeinfo is %p, addr_of_ptr_slot is %p, ptr_slot_val is %p\n",
	          //    body, e.offset, e.typeinfo, oldslot, *oldslot);
	          // recursively copy the field from cell, yielding subfwdaddr
	          // set the copied cell field to subfwdaddr
	          if (*oldslot != NULL) {
	            void** newslot = (void**) offset(new_addr->body(), e.offset);
	            *newslot = copy(*oldslot, e.typeinfo);
	          }
	        }

	        {
	          struct tuple_t { void* l, *r; int s; };
	          tuple_t& t1 = * (tuple_t*)body;
              tuple_t& t2 = * (tuple_t*)new_addr->body();
              fprintf(gclog, "%p : {%p, %p, %d} -> %p: { %p , %p, %d }\n", body,
                  t1.l, t1.r, t1.s, new_addr->body(), t2.l, t2.r, t2.s);
	        }
	      }

	      return cell->get_forwarded_body();
	    } else {
	      printf("not enough space to copy! have %lld, need %lld\n", free_size(), size);
	      //exit(255);
	      return NULL;
	    }
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
  copying_gc(int64_t size) {
	curr = new semispace(size, this);

	// Allocate some temporary memory to force curr and next
	// to have visually distinct address ranges.
	std::vector<semispace*> stretches;
	for (int i = (4 * 1000 * 1000) / size; i >= 0; --i) {
	  stretches.push_back(new semispace(size, this));
	}
	next = new semispace(size, this);
	for (int i = 0; i < stretches.size(); --i) {
      delete stretches[i]; stretches[i] = NULL;
    }

	num_allocations = 0;
	num_collections = 0;
  }

  ~copying_gc() {
	fprintf(gclog, "num allocations: %d, num collections: %d\n",
			num_allocations, num_collections);
  }

  void force_gc_for_debugging_purposes() { this->gc(); }

  const char* describe(void* ptr) {
    if (curr->contains(ptr)) return "curr";
    if (next->contains(ptr)) return "next";
    return "unknown";
  }

  bool is_probable_stack_pointer(void* suspect, void* knownstackaddr) {
    if (curr->contains(suspect) || next->contains(suspect)) return false;
    return (labs(((char*)suspect) - (char*)knownstackaddr) < (1<<20));
  }

  // copy the cell at the given address to the next semispace
  void* copy(void* body, const void* meta) {
    return next->copy(body, meta);
  }

  // update slots in the body containing pointers to heap cells
  void update(void* body, const void* meta) {
    next->update(body, meta);
  }

  void* allocate(int64_t size) {
	++num_allocations;

	if (curr->can_allocate(size)) {
	  return curr->allocate_prechecked(size);
	} else {
	  gc();
	  if (curr->can_allocate(size)) {
	    printf("gc collection freed space, now have %lld\n", curr->free_size());
		return curr->allocate_prechecked(size);
	  } else {
	    printf("working set exceeded heap size! aborting...\n");
	    exit(255);
	    return NULL;
	  }
	}
  }
};

copying_gc* allocator = NULL;

void copying_gc_root_visitor(void **root, const void *meta) {
  void* body = *root;
  if (body) {
    fprintf(gclog, "gc root@%p visited: %p, meta: %p\n", root, body, meta);

    if (allocator->is_probable_stack_pointer(body, root)) {
      fprintf(gclog, "found stack pointer\n");
      if (meta) {
        typemap* map = (typemap*) meta;
        fprintf(gclog, "name is %s, # ptrs is %d\n", map->name, map->numPointers);
      }

      allocator->update(body, meta);
    } else {
      void* newaddr = allocator->copy(body, meta);
      if (meta) {
        typemap* map = (typemap*) meta;
        fprintf(gclog, "\tname: %s", map->name);
      }
      if (newaddr) {
        fprintf(gclog, "; replacing %p with %p\n", body, newaddr);
        *root = newaddr;
      }
    }
  }
}

void copying_gc::gc() {
  ++num_collections;

#if USE_FOSTER_GC_PLUGIN
  visitGCRootsWithStackMaps(copying_gc_root_visitor);
#else
  // copy all used blocks to the next semispace
  visitGCRoots(copying_gc_root_visitor);
#endif

  flip();

  next->clear(); // for debugging purposes

  fprintf(gclog, "\t/gc\n");
  fflush(gclog);
}

#if USE_FOSTER_GC_PLUGIN
std::map<void*, const stackmap::PointCluster*> clusterForAddress;

void register_stackmaps() {
  int32_t numStackMaps = __foster_gcmaps.numStackMaps;
  fprintf(gclog, "num stack maps: %d\n", numStackMaps);

  void* ps = (void*) __foster_gcmaps.stackmaps;
  size_t totalOffset = 0; // 

  for (int32_t m = 0; m < numStackMaps; ++m) {
    const stackmap& s = *(const stackmap*) offset(ps, totalOffset);
    int32_t numClusters = s.pointClusterCount; 
    fprintf(gclog, "  num clusters: %d\n", numClusters);

    totalOffset += sizeof(s.pointClusterCount);

    for (int32_t i = 0; i < numClusters; ++i) {
      const stackmap::PointCluster* pc =
        (const stackmap::PointCluster*) offset(ps, totalOffset);
      const stackmap::PointCluster& c = *pc;
      totalOffset += sizeof(int32_t) * 4 // sizes + counts
                   + sizeof(int32_t) * c.liveCountWithoutMetadata
                   + sizeof(stackmap::OffsetWithMetadata)
                                     * c.liveCountWithMetadata;
      void** safePointAddresses = (void**) offset(ps, totalOffset);
      totalOffset += sizeof(void*)   * c.addressCount;

      for (int32_t i = 0; i < c.addressCount; ++i) {
        void* safePointAddress = safePointAddresses[i];
        clusterForAddress[safePointAddress] = pc;
      }

      fprintf(gclog, "    cluster fsize %d, & %d, live: %d + %d\n",
		     c.frameSize, c.addressCount,
		     c.liveCountWithMetadata, c.liveCountWithoutMetadata);
    }
  }
}
#endif

base::TimeTicks start;

void initialize() {
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  const int KB = 1024;
  allocator = new copying_gc(1 * KB);

#if USE_FOSTER_GC_PLUGIN
  register_stackmaps(); 
#endif

  start = base::TimeTicks::HighResNow();
}

void cleanup() {
  base::TimeDelta elapsed = base::TimeTicks::HighResNow() - start;
  fprintf(gclog, "Elapsed runtime: %lld.%lld s\n",
		  elapsed.InSeconds(), elapsed.InMilliseconds() - (elapsed.InSeconds() * 1000));

  delete allocator;
}

std::string format_ref(void* ptr) {
  static char buf[64];
  // TODO add method lock
  sprintf(buf, "%p - (%s)", ptr, allocator->describe(ptr));
  return std::string(buf);
}

extern "C" void* memalloc(int64_t sz) {
  return allocator->allocate(sz);
}

extern "C" void force_gc_for_debugging_purposes() {
  allocator->force_gc_for_debugging_purposes();
}

#if USE_FOSTER_GC_PLUGIN
struct frameinfo { frameinfo* frameptr; void* retaddr; };
int backtrace_x86_32(frameinfo* frames, size_t sz) {
  frameinfo* frame = (frameinfo*) __builtin_frame_address(0);
  int i = 0;
  while (frame && sz --> 0) {
    frames[i] = (*frame);
    frame     = (*frame).frameptr;
    ++i;
  }
  return i;
}

void visitGCRootsWithStackMaps(void (*visitor)(void **root, const void *meta)) {
  enum { MAX_NUM_RET_ADDRS = 1024 };
  static void* retaddrs[MAX_NUM_RET_ADDRS];
  static frameinfo frames[MAX_NUM_RET_ADDRS];

  int nFrames = backtrace_x86_32(frames, MAX_NUM_RET_ADDRS);

  const bool SANITY_CHECK_CUSTOM_BACKTRACE = true;
  if (SANITY_CHECK_CUSTOM_BACKTRACE) {
    int numRetAddrs = backtrace((void**)&retaddrs, MAX_NUM_RET_ADDRS);
#if 0
    for (int i = 0; i < numRetAddrs; ++i) {
      fprintf(gclog, "backtrace: %p\n",  retaddrs[i]);
    }
    for (int i = 0; i < nFrames; ++i) {
      fprintf(gclog, "           %p\n", frames[i].retaddr);
    }
#endif

    int diff = numRetAddrs - nFrames;
    for (int i = 0; i < numRetAddrs; ++i) {
      if (frames[i].retaddr != retaddrs[diff + i]) {
        fprintf(gclog, "custom + system backtraces disagree: %p vs %p, diff %d\n", frames[diff + i].retaddr, retaddrs[i], diff);
        exit(1);
      }
    }
  }

  // For now, we must disable frame pointer elimination
  // to ensure that we can calculate the stack pointer
  // (which requires that we have a frame pointer).
  // It would be nice to eventually allow FPE and use debug
  // info (unwind tables) to reconstruct frame sizes.
  // But, judging by
  // http://mituzas.lt/2009/07/26/on-binaries-and-fomit-frame-pointer/
  // the performance gain from FPE is only on the order of
  // 1 to 3%, so it's not a critical optimization.
  //
  // Note that while LLVM's GC plugin architecture tells us
  // frame sizes for Foster functions, and thus lets us
  // theoretically reconstruct frame boundaries once we
  // reach the land of Foster, we still need "a few"
  // frame pointers to get from Here to There.
  //
  // If we were willing to accept a dependency on libgcc,
  // we could reuse the _Unwind_Backtrace function to unwind
  // past libfoster frames and then use LLVM's computed
  // stack frame sizes to crawl the rest of the stack.

  for (int i = 0; i < nFrames; ++i) {
    void* safePointAddr = frames[i].retaddr;
    void* frameptr = (void*) frames[i].frameptr;
    
    const stackmap::PointCluster* pc = clusterForAddress[safePointAddr];
    if (!pc) continue;

    int32_t frameSize = pc->frameSize;

    for (int a = 0; a < pc->liveCountWithMetadata; ++a) {
      int32_t off = pc->liveOffsetsWithMetadata[a].offset;
      const void* meta = pc->liveOffsetsWithMetadata[a].metadata;
      void* rootaddr = offset(frameptr, off);
      visitor((void**) rootaddr, meta);
    }
  }

}
#endif

#if 0
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

} } } // namespace foster::runtime::gc

