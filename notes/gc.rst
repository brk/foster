Garbage Collection
------------------

Memory management is an ongoing topic of experimentation.

As of early 2020, prior approaches had been rolled back to a relatively
minimal baseline approach: stack-conservative Immix [Sha2014]_. The primary benefit
of being stack-conservative is that it (A) does not inhibit LLVM's
low level optimizations, and (B) allows using non-custom builds of LLVM.
Immix is a nice baseline in part due to its design (which is relatively simple,
and does a good job of balancing the tension between per-object and per-heap
focus), and in part because many extensions of Immix have already been explored
in the literature, making it easier to potentially expore/adopt such directions
in the future.

.. [Sha2014] https://www.microsoft.com/en-us/research/publication/fast-conservative-garbage-collection/


Heap Layout
~~~~~~~~~~~

A heap cell consists of a pointer-sized header, followed by a body.
The header may be either an integer which represents the size of the body,
or a pointer to a type map for the body, which contains offsets for the
pointers contained in the body, along with type maps for the contents of
those pointers.

Typeinfo maps are aligned to at least a multiple of 8, yielding
3 bits in the header pointer. One bit is used to mark forwarding pointers.
The other bits are reserved for future implementation usage.

..
  One bit is used to mark objects which should be updated rather than moved;
  for example, objects allocated on the stack or via malloc instead of through
  a bump-pointer alloctor. The third bit is not yet allocated.
  [[ TODO implement this :) ]]

Diagram::

    [Object *-]-+
    [Reference] |
                v
      +--------+----------+----------+
      | header |    f1    |    f2   ...
      |  ptr * |          |         ...
      +------|-+----------+----------+
             |
             v
          struct {
            i64         cellSize;
            i8*         typeName;
            i32         numPtrEntries;
            i8          isCoro;
            i8          isArray = false;
            struct { i8* typeinfo; i32 offset }[numPtrEntries];
          }

References to objects are implemented as pointers to the body (first field).
When scanning objects, the GC may convert a body pointer into a heap-cell
pointer by subtracting ``sizeof(void*)``.

An array has a slightly different representation::

    [Object *-]-+
    [Reference] |
                v
      +--------+-----------+----------+----------+
      | header | array     |   e1     |    e2   ...
      |  ptr * | size word |          |         ...
      +------|-+-----------+----------+----------+
             |
             v
          struct {
            i64         cellSize;
            i8*         typeName;
            i32         numPtrEntries;
            i8          isCoro;
            i8          isArray = true;
            struct { i8* typeinfo; i32 offset }[numPtrEntries];
          }

There are three cases for the elements worth considering:

  * Non-pointer POD types, or structs thereof. No GC action necessary.
  * Struct containing pointers. GC loops for each element,
    computes aligned element start position and recurses at offsets.
  * Pointer. As above.

Values of an algebraic data type with multiple constructors
currently store their associated constructor in the type metadata::

    [Object *-]-+
    [Reference] |
                v
      +--------+----------+----------+
      | header |    f1    |    f2   ...
      |  ptr * |          |         ...
      +------|-+----------+----------+
             |
             v
          struct {
            i64         cellSize;
            i8*         typePlusCtorName;
            i32         numPtrEntries;
            i8          ctorId = C;
            i8          isCoro;
            i8          isArray = false;
            struct { i8* typeinfo; i32 offset }[numPtrEntries];
          }

It would be possible to store the constructor tag in
either the body or header payloads.

.. 
  Stable Pointers
  ~~~~~~~~~~~~~~~

  Interfacing with C code requires an alternative to a compacting or copying
  garbage collector, because the moving GC will be unable to update pointers
  held by external C code.

  One simple option would be to track which pointers can flow to external C
  functions (that is, those which are conservatively assumed to capture args),
  and ensure that those pointers are allocated from a reference-counted heap.

  However, that would open up race conditions between concurrently-executing
  Foster code and C code. What we really want is make sure that any object
  reachable from C code has a stable address. Address-stability can (I think)
  be tracked as an effect. However, it must be implemented for a lower-level
  IR which makes allocation explicit.

  On the other hand, "hiding" such an allocation decision behind an effect
  may be misguided; perhaps it's better to simply expose stable pointers as
  an explicit data type, along the lines of Haskell's FFI?

..
  Coroutines and Garbage Collection
  +++++++++++++++++++++++++++++++++

  Coroutines somewhat complicate the details of garbage collection.

  First, a garbage collection invoked from an
  active coroutine must not only walk the call stack to trace roots,
  it must also go through the stack of suspended coroutines and trace
  roots from each saved continuation point.
  Second, any reachable dormant coroutine must also be traced.

  This implies that it's somewhat nicer to represent the stack
  of suspended coroutines via a linked list threaded through the
  coroutine objects, rather than as a separate stack data structure,
  because the former representation meshes better with the GC's notion
  of reachability.

  Another point is that coroutine stacks should not be allocated on
  a compacting (/semispace) GC heap. Otherwise, when a GC is triggered
  from a coroutine, the GC must (A) detect when its stack has been copied,
  and (B) update the stack pointer + base pointer to refer to the new copy.
  It's not impossible to do, but it's easier to just avoid the mess entirely.

  The easiest solution for coroutine stacks is probably to maintain a
  separate mark-sweep heap: when a coroutine is traced, its stack is marked,
  and once all stacks have been marked, unmarked stacks may be ``free()``\d.
  Thankfully, performance is of no consideration for tracking the coroutine
  stacks, under the assumption that coroutines will be allocated (and freed)
  an order of magnitude less frequently than "regular" objects.


