Garbage Collection
==================

Heap Layout
-----------

A heap cell consists of a pointer-sized header, followed by a body.
The header may be either an integer which represents the size of the body,
or a pointer to a type map for the body, which contains offsets for the
pointers contained in the body, along with type maps for the contents of
those pointers.

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


