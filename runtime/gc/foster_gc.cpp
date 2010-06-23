#include <inttypes.h>
#include <cstdlib>
#include <cstdio>
#include <cstring>

#include "foster_gc.h"

#include "base/time.h"

// extract frame pointer (libunwind or llvm.frameaddress?)
// lookup stack map based on fp
//

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

void visitGCRoots(void (*visitor)(void **root, const void *meta));

FILE* gclog = NULL;

class copying_gc {
  class semispace {
	  semispace(int64_t size) {
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
	  bool contains(void* ptr) {
	    return (ptr >= start) && (ptr < end);
	  }

	  void clear() { memset(start, 255, end - start); }

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

	  // returns body of newly allocated cell
	  void* copy(void* body, const void* meta) {
	    heap_cell* cell = HEAP_CELL_FOR_BODY(body);

	    if (cell->is_forwarded()) {
	      return cell->get_forwarded_body();
	    }

	    int64_t size = cell->size();

	    if (can_allocate(size)) {
	      memcpy(bump, cell, size);
	      heap_cell* new_addr = (heap_cell*) bump;
	      bump += size;

	      cell->set_forwarded_body(new_addr->body());

	      if (meta) {
	        const typemap* map = (const typemap*) meta;
	        const char* bodybytes = (const char*) body;
	        struct tuple_t { void* l, *r; int s; };


	        // for each pointer field in the cell
	        for (int i = 0; i < map->numPointers; ++i) {
	          const typemap::entry& e = map->entries[i];
	          char* oldbodybytes = (char*) body;
	          void** old_ptr_slot    = (void**) &oldbodybytes[e.offset];
	          void* old_ptr_slot_val = (void*) *old_ptr_slot;

	          //fprintf(gclog, "body is %p, offset is %d, typeinfo is %p, addr_of_ptr_slot is %p, ptr_slot_val is %p\n",
	          //    body, e.offset, e.typeinfo, addr_of_ptr_slot, ptr_slot_val);
	          // recursively copy the field from cell, yielding subfwdaddr
	          // set the copied cell field to subfwdaddr
	          if (old_ptr_slot_val != NULL) {
	            char* newbodybytes = (char*) new_addr->body();
	            void** newslot = (void**) &newbodybytes[e.offset];
	            *newslot = copy(old_ptr_slot_val, e.typeinfo);
	          }
	        }
	        {
	          tuple_t& t1 = * (tuple_t*)body;
              tuple_t& t2 = * (tuple_t*)new_addr->body();
              fprintf(gclog, "%p : {%p, %p, %d} -> %p: { %p , %p, %d }\n", body,
                  t1.l, t1.r, t1.s, new_addr->body(), t2.l, t2.r, t2.s);
	        }
	      } else {
	        fprintf(gclog, "called copy with null metadata\n");
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
	curr = new semispace(size);

	// Allocate some temporary memory to force curr and next
	// to have visually distinct address ranges.
	std::vector<semispace*> stretches;
	for (int i = (4 * 1000 * 1000) / size; i >= 0; --i) {
	  stretches.push_back(new semispace(size));
	}
	next = new semispace(size);
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

  const char* describe(void* ptr) {
    if (curr->contains(ptr)) return "curr";
    if (next->contains(ptr)) return "next";
    return "unknown";
  }

  // copy the cell at the given address to the next semispace
  void* copy(void* body, const void* meta);

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
  void* cell = *root;
  if (cell) {
    void* newaddr = allocator->copy(cell, meta);

    fprintf(gclog, "gc root visited: %p, meta: %p", cell, meta);
    if (meta) {
      typemap* map = (typemap*) meta;
      fprintf(gclog, "\tname: %s", map->name);
    }
    fprintf(gclog, "; replacing %p with %p\n", cell, newaddr);
    *root = newaddr;
  }
}

void* copying_gc::copy(void* cell, const void* meta) {
  return next->copy(cell, meta);
}

void copying_gc::gc() {
  ++num_collections;
  // copy all used blocks to the next semispace
  visitGCRoots(copying_gc_root_visitor);
  flip();

  // for debugging purposes
  next->clear();
  // TODO clobbering the oldspace gives segfaults, which
  // implies that we didn't update some pointers when we copied...

  fprintf(gclog, "\t/gc\n");
  fflush(gclog);
}

base::TimeTicks start;

void initialize() {
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  const int KB = 1024;
  allocator = new copying_gc(1 * KB);

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

void visitGCRoots(void (*Visitor)(void **Root, const void *Meta)) {
  for (StackEntry *R = llvm_gc_root_chain; R; R = R->Next) {
    unsigned i = 0;
    
    // For roots [0, NumMeta), the metadata pointer is in the FrameMap.
    for (unsigned e = R->Map->NumMeta; i != e; ++i)
      Visitor(&R->Roots[i], R->Map->Meta[i]);
    
    // For roots [NumMeta, NumRoots), the metadata pointer is null.
    for (unsigned e = R->Map->NumRoots; i != e; ++i) {
      Visitor(&R->Roots[i], NULL);
    }
  }
}

} } } // namespace foster::runtime::gc

