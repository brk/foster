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
