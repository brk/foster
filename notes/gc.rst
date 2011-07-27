Garbage Collection
==================

Heap Layout
-----------

A heap cell consists of a pointer-sized header, followed by a body.
The header may be either an integer which represents the size of the body,
or a pointer to a type map for the body, which contains offsets for the
pointers contained in the body, along with type maps for the contents of
those pointers.

Typeinfo maps are aligned to at least a multiple of 8, yielding
3 bits in the header pointer. One bit is used to mark forwarding pointers.
One bit is used to mark objects which should be updated rather than moved;
for example, objects allocated on the stack or via malloc instead of through
a bump-pointer alloctor. [[ TODO implement this :) ]]

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

An algebraic data type with multiple constructors likely needs a third
representation, sufficient to distinguish which constructor was used to
build the object. One possibility::


    [Object *-]-+
    [Reference] |
                v
      +--------+----------+----------+----------+
      | header |          |    f1    |    f2   ...
      |  ptr * |   ctor   |          |         ...
      +------|-+----------+----------+----------+
             |
             v
          struct {
            i64         cellSize;
            i8*         typePlusCtorName;
            i32         numPtrEntries;
            i8          isCoro;
            i8          isArray = false;
            struct { i8* typeinfo; i32 offset }[numPtrEntries];
          }

There are a number of potential variations on the above sketch:

 #. Ctor bits could be stored in (A) the object reference,
    (B) the header pointer, or (C, shown) a designated constructor field.
 #. The header pointer could describe the overall type (with cell size equal to
    the largest-layout variant) or the specific variant.
 #. As a special case, data types with one nullary variant can have
    a plain pointer representation.

With a variant-specific typeinfo pointer, extra ctor tag bits are not
strictly needed, as the pointer itself could be used in a switch (or
at least an if-cascade, since converting a global var addr to constant int
**may** not be kosher). Or the struct of typeinfo could be extended with an
i8 ctorTag field.


Stable Pointers
---------------

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
