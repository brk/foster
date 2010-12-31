// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cstddef> // for offsetof

#include "foster_gc.h"
#include "libfoster_gc_roots.h"
#include "_generated_/FosterConfig.h"

#include "base/time.h"
#include "base/platform_thread.h"

#include "execinfo.h"

#define TRACE do { fprintf(gclog, "%s::%d\n", __FILE__, __LINE__); fflush(gclog); } while (0)

/////////////////////////////////////////////////////////////////

#include <sstream>
#include <list>
#include <vector>
#include <map>

namespace foster {
namespace runtime {
namespace gc {

// Performs byte-wise addition on void pointer base
void* offset(void* base, int off) {
  return (void*) (((char*) base) + off);
}

// This structure describes the layout of a particular type,
// giving offsets and type descriptors for the pointer slots.
struct typemap {
  const char* name;
  int32_t numPointers;
  struct entry {
    const void* typeinfo;
    int32_t offset;
  };
  entry entries[0];
};

struct stackmap {
  struct OffsetWithMetadata {
    void* metadata;
    int32_t offset;
  };
  // GC maps emit structures without alignment, so we can't simply
  // use sizeof(stackmap::OffsetWithMetadata), because that value
  // includes padding.

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
  struct PointCluster {
    // register_stackmaps() assumes it knows the layout of this struct!
    int32_t frameSize;
    int32_t addressCount;
    int32_t liveCountWithMetadata;
    int32_t liveCountWithoutMetadata;
    OffsetWithMetadata
            liveOffsetsWithMetadata[0];
    int32_t liveOffsetsWithoutMetadata[0];
    void*   safePointAddresses[0];

    // Use manual pointer arithmetic to avoid C's padding rules.
    const OffsetWithMetadata* offsetWithMetadata(int i) const {
      #define OFFSET_WITH_METADATA_SIZE (sizeof(void*) + sizeof(int32_t))
      return (const OffsetWithMetadata*)
                  offset((void*) liveOffsetsWithMetadata,
                         i * OFFSET_WITH_METADATA_SIZE);
    }

    // TODO provide similar methods to find actual
    // addresses of the other flexible arrays.
  };
  PointCluster pointClusters[0];
};

struct stackmap_table {
  int32_t numStackMaps;
  stackmap stackmaps[0];
};

// This symbol is emitted by the fostergc LLVM GC plugin to the
// final generated assembly.
extern "C" {
  extern stackmap_table foster__gcmaps;
}

////////////////////////////////////////////////////////////////////
const uint64_t FORWARDED_BIT = 0x02; // 0b000..00010
#define HEAP_CELL_HEADER_SIZE (sizeof(int64_t))

struct heap_cell {
  int64_t       _size;
  unsigned char _body[0];
  //======================================
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

  static heap_cell* for_body(void* ptr) {
    return (heap_cell*) offset(ptr, -HEAP_CELL_HEADER_SIZE);
  }
};


typedef void (*gc_visitor_fn)(void** root, const void* meta);

void visitGCRootsWithStackMaps(void* start_frame,
                               gc_visitor_fn visitor);

FILE* gclog = NULL;

class copying_gc {
  class semispace {
  public:
      semispace(int64_t size, copying_gc* parent) : parent(parent) {
        start = (char*) malloc(size);
        end   = start + size;
        bump  = start;

        genericClosureMarker = NULL;
      }

      ~semispace() {
        free(start);
      }
  private:
      char* start;
      char* end;
      char* bump;
      copying_gc* parent;

      char* genericClosureMarker;

  public:
      void reset_bump() { bump = start; }

      bool contains(void* ptr) {
        return (ptr >= start) && (ptr < end);
      }

      void clear() {
        fprintf(gclog, "clearing mem from %p to %p\n", start, end);
        fflush(gclog);
        memset(start, 255, end - start);
      }

      int64_t free_size() { return end - bump; }

      bool can_allocate(int64_t body_size) {
        return end > bump + body_size + HEAP_CELL_HEADER_SIZE;
      }

      void* allocate_prechecked(int64_t body_size) {
        heap_cell* allot = (heap_cell*) bump;
        bump += body_size + HEAP_CELL_HEADER_SIZE;
        allot->set_size(body_size);
        return allot->body();
      }

      // Prerequisite: body is a stack pointer.
      // Behavior:
      // * Any slots containing stack pointers should be recursively update()ed.
      // * Any slots containing heap pointers should be
      //   overwritten with copy()'d values.
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
          void** envptr_slot = (void**) offset(body, sizeof(void*));
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
            body, e.offset, oldslot, *oldslot, e.typeinfo); fflush(gclog);
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
        const int ptrsize = sizeof(void*);
        if (!meta) {
          void** bp4 = (void**) offset(body, ptrsize);
          fprintf(gclog, "called copy with null metadata\n"); fflush(gclog);
          fprintf(gclog, "body   is %p -> %p\n", body, *(void**)body); fflush(gclog);
          fprintf(gclog, "body+%d is %p -> %p\n", ptrsize, offset(body, ptrsize), *bp4); fflush(gclog);
          fprintf(gclog, "body-%d is %p -> %p\n", ptrsize, offset(body,-ptrsize), *(void**)offset(body,-ptrsize));
          fflush(gclog);
          void** envptr = (void**)*bp4;
          fprintf(gclog, "envptr: %p -> %p\n", envptr, *envptr); fflush(gclog);
          typemap* envtm = (typemap*) *envptr;
          fprintf(gclog, "env tm name is %s, # ptrs = %d\n", envtm->name, envtm->numPointers); fflush(gclog);
          return NULL;
        }

        heap_cell* cell = heap_cell::for_body(body);

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
          printf("not enough space to copy!\n");
          printf("have %llu = 0x%llx\n", free_size(), (unsigned long long) free_size());
          printf("need %llu = 0x%llx\n", size,        (unsigned long long) size);
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
    curr->reset_bump();
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

  // TODO this is just wrong in the presence of heap-allocated
  // stack frames for coroutines! :(
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
        exit(255); // TODO be more careful if we're allocating from a coro...
        return NULL;
      }
    }
  }
};

copying_gc* allocator = NULL;

// This function statically references the global allocator.
// Eventually we'll want a generational GC with thread-specific
// allocators and (perhaps) type-specific allocators.
void copying_gc_root_visitor(void **root, const void *meta) {
  void* body = *root;
  if (body) {
    fprintf(gclog, "gc root@%p visited, body: %p, meta: %p\n", root, body, meta);

    if (allocator->is_probable_stack_pointer(body, root)) {
      //       |------------|
      // root: |    body    |---\
      //       |------------|   |
      // body: |            |<--/
      //       |            |
      //       |            |
      //       |------------|
      fprintf(gclog, "found stack pointer\n");
      if (meta) {
        typemap* map = (typemap*) meta;
        fprintf(gclog, "name is %s, # ptrs is %d\n", map->name, map->numPointers);
      }

      allocator->update(body, meta);
    } else {
      //       |------------|            |------------|
      // root: |    body    |---\        |    _size   |
      //       |------------|   |        |------------|
      //                        \------> |            |
      //                                 |            |
      //                                 |            |
      //                                 |------------|
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

void visitCoro(foster_generic_coro** coro, gc_visitor_fn visitor);

void copying_gc::gc() {
  ++num_collections;

  visitGCRootsWithStackMaps(__builtin_frame_address(0),
                            copying_gc_root_visitor);

  visitCoro(&current_coro, copying_gc_root_visitor);
  // TODO update current_coro to point to the newspace copy.

  flip();
  next->clear(); // for debugging purposes
  fprintf(gclog, "\t/gc\n");
  fflush(gclog);
}

std::map<void*, const stackmap::PointCluster*> clusterForAddress;

// Stack map registration walks through the stack maps emitted
// by the Foster LLVM GC plugin
void register_stackmaps() {
  int32_t numStackMaps = foster__gcmaps.numStackMaps;
  fprintf(gclog, "num stack maps: %d\n", numStackMaps); fflush(gclog);

  void* ps = (void*) foster__gcmaps.stackmaps;
  size_t totalOffset = 0;

  for (int32_t m = 0; m < numStackMaps; ++m) {
    const stackmap* stackmap_ptr = (const stackmap*) offset(ps, totalOffset);
    fprintf(gclog, "  stackmap_ptr: %p\n", stackmap_ptr); fflush(gclog);
    const stackmap& s = *stackmap_ptr;
    int32_t numClusters = s.pointClusterCount;
    fprintf(gclog, "  num clusters: %d\n", numClusters); fflush(gclog);

    totalOffset += sizeof(s.pointClusterCount);

    for (int32_t i = 0; i < numClusters; ++i) {
      const stackmap::PointCluster* pc =
        (const stackmap::PointCluster*) offset(ps, totalOffset);
      fprintf(gclog, "  pointcluster*: %p\n", pc); fflush(gclog);

      const stackmap::PointCluster& c = *pc;
      totalOffset += sizeof(int32_t) * 4 // sizes + counts
                   + sizeof(int32_t) * c.liveCountWithoutMetadata
                   + OFFSET_WITH_METADATA_SIZE * c.liveCountWithMetadata;

      void** safePointAddresses = (void**) offset(ps, totalOffset);
      totalOffset += sizeof(void*)   * c.addressCount;

      fprintf(gclog, "  safePointAddrs: %p * %d\n", safePointAddresses, c.addressCount); fflush(gclog);
      fprintf(gclog, "  sizeof(stackmap::OffsetWithMetadata): %lu\n", sizeof(stackmap::OffsetWithMetadata));
      fprintf(gclog, "  OFFSET_WITH_METADATA_SIZE: %lu\n", OFFSET_WITH_METADATA_SIZE);
      fprintf(gclog, "  c.liveCountWithMetadata: %d\n", c.liveCountWithMetadata);

      for (int32_t i = 0; i < c.addressCount; ++i) {
        void* safePointAddress = safePointAddresses[i];
        clusterForAddress[safePointAddress] = pc;
      }

      fprintf(gclog, "    cluster fsize %d, & %d, live: %d + %d\n",
                     c.frameSize, c.addressCount,
                     c.liveCountWithMetadata, c.liveCountWithoutMetadata);
    }
  }
  fprintf(gclog, "--------- gclog stackmap registration complete ----------\n");
  fflush(gclog);
}

base::TimeTicks start;

void initialize() {
  gclog = fopen("gclog.txt", "w");
  fprintf(gclog, "----------- gclog ------------\n");

  const int KB = 1024;
  allocator = new copying_gc(1024 * KB);

  register_stackmaps();

  start = base::TimeTicks::HighResNow();
}

void cleanup() {
  base::TimeDelta elapsed = base::TimeTicks::HighResNow() - start;
  fprintf(gclog, "Elapsed runtime: %ld.%ld s\n",
                  long(elapsed.InSeconds()),
          long(elapsed.InMilliseconds() - (elapsed.InSeconds() * 1000)));

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

void force_gc_for_debugging_purposes() {
  allocator->force_gc_for_debugging_purposes();
}

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
int backtrace_x86(frameinfo* frame, frameinfo* frames, size_t frames_sz) {
  int i = 0;
  while (frame && frames_sz --> 0) {
    if (0) {
      fprintf(gclog, "frame: %p\n", frame);
      if (frame) {
        fprintf(gclog, "frameptr: %p, retaddr: %p\n", frame->frameptr, frame->retaddr);
      }
      fflush(gclog);
    }
    frames[i] = (*frame);
    frame     = (*frame).frameptr;
    ++i;
  }
  return i;
}

void visitGCRootsWithStackMaps(void* start_frame,
                               gc_visitor_fn visitor) {
  enum { MAX_NUM_RET_ADDRS = 1024 };
  static void* retaddrs[MAX_NUM_RET_ADDRS];
  static frameinfo frames[MAX_NUM_RET_ADDRS];

  // Collect frame pointers and return addresses
  // for the current call stack.
  int nFrames = backtrace_x86((frameinfo*) start_frame, frames, MAX_NUM_RET_ADDRS);
  const bool SANITY_CHECK_CUSTOM_BACKTRACE = false;
  if (SANITY_CHECK_CUSTOM_BACKTRACE) {
    // backtrace() seems to fail when called from a coroutine's stack...
    int numRetAddrs = backtrace((void**)&retaddrs, MAX_NUM_RET_ADDRS);
#if 1
    for (int i = 0; i < numRetAddrs; ++i) {
      fprintf(gclog, "backtrace: %p\n", retaddrs[i]);
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

  // Use the collected return addresses to look up a safe point
  // cluster map, which gives offsets from the corresponding
  // frame pointer at which we will find pointers to be scanned.

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
      int32_t     off  = pc->offsetWithMetadata(a)->offset;
      const void* meta = pc->offsetWithMetadata(a)->metadata;
      void* rootaddr = offset(frameptr, off);
      visitor((void**) rootaddr, meta);
    }
    // TODO also scan pointers without metadata
  }
}

void* topmost_frame_pointer(foster_generic_coro* coro) {
  // If the coro status is "running", we should scan the coro
  // but not its stack (since the stack will be examined from ::gc()).
  // TODO when multithreading, running coros should be stamed with
  // the id of the thread running them, so that other threads will
  // know not to scan underneath another running thread.
  foster_assert(coro->status == FOSTER_CORO_SUSPENDED
             || coro->status == FOSTER_CORO_DORMANT,
           "can only get topmost frame pointer from "
           "suspended or dormant coro!");
  void** sp = coro->ctx.sp;
  #if __amd64
  const int NUM_SAVED = 6;
  #else // CORO_WIN_TIB : += 3
  const int NUM_SAVED = 4;
  #endif

  return sp[NUM_SAVED - 1];
}

void visitCoro(foster_generic_coro** coro_addr,
               gc_visitor_fn visitor) {
  foster_generic_coro* coro = *coro_addr;

  if (!coro) {
    return;
  }

  #ifdef FOSTER_MULTITHREADED
  if (coro->status == FOSTER_CORO_RUNNING) {
    // Don't scan a coroutine if it's being run by another thread!
    if (coro->owner_thread != PlatformThread::CurrentId()) {
      return;
    }
  }
  #endif

  if (coro->status == FOSTER_CORO_INVALID
   || coro->status == FOSTER_CORO_DEAD) {
    // No need to scan the coro or its stack...
    return;
  }

  // If we've made it this far, then the coroutine is owned by us,
  // and is either dormant, suspended, or running. We won't scan
  // the stack of a running coro, since we should already have done so.
  // But we will trace back the coro invocation chain and scan other stacks.

  // Another point worth mentioning is that two generic_coros
  // may point to the same stack but have different statuses:
  // an fcoro may say "RUNNING" while a ccoro may say "SUSPENDED",
  // because we don't bother updating the status for the current coro
  // when we invoke away from it. But since fcoros are the only ones
  // referenced directly by the program, it's all OK.

  heap_cell* cell = heap_cell::for_body(coro);
  if (cell->is_forwarded()) {
    // if coro has fwding ptr, update coro addr
    *coro_addr = (foster_generic_coro*) cell->get_forwarded_body();
  } else {
    // otherwise, copy the coro to the newspace,
    // set the forwarding pointer, and scan the
    // coro.
    // TODO don't assume there's a single global allocator
    void* coro_metadata = NULL;
    //void* newbody = allocator->copy(body, coro_metadata);
  }

  fprintf(gclog, "coro %p, status: %d\n", coro, coro->status);

  // TODO handle arg

TRACE;

  // Note! We scan stacks from ccoros (yielded to),
  // not fcoros (invokable). A suspended stack will have
  // pointers into the stack from both types of coro, but
  // the ccoro pointer will point higher up the stack!
  if (coro->fn) {
    // Scan the sibling, which will also end up scanning
    // the suspended stack which we invoked from.
    visitCoro((foster_generic_coro**) &coro->sibling,
              visitor);

    // Once that's done, proceed up the invocation chain.
    visitCoro((foster_generic_coro**) &coro->invoker,
              visitor);
  } else {
    // TODO mark stack so it won't be swept away

    // extract frame pointer from ctx, and visit its stack.
    void* frameptr = topmost_frame_pointer(coro);
    foster_assert(frameptr != NULL, "(c)coro frame ptr shouldn't be NULL!");
    visitGCRootsWithStackMaps(frameptr, visitor);
  }
}

/////////////////////////////////////////////////////////////////

} } } // namespace foster::runtime::gc

