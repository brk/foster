Garbage Collection
==================

Heap Layout
-----------

A heap cell consists of a pointer-sized header, followed by a body.
The header may be either an integer which represents the size of the body,
or a pointer to a type map for the body, which contains offsets for the
pointers contained in the body, along with type maps for the contents of
those pointers.

References to objects are implemented as pointers to the body.
When scanning objects, the GC may convert a body pointer into a heap-cell
pointer by subtracting ``sizeof(void*)``.
