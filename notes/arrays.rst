Arrays
======

TODO: fancy DML-style dependent types for array indexing.

Pessimizations and Optimizations
--------------------------------

As a C++ programmer, it is natural to think of arrays as storing unboxed values.
However, copying garbage collection and algebraic data types both complicate
that initial picture. Variant types imply that storage for array slots must be
conservatively sized in the worst case, and also that, from the GC's
perspective, there are only two kinds of arrays: those which have metadata
pointers per-slot, and those which do not (byte arrays, etc).

Copying GC means that, as array slots are derived pointers, it is very tricky to
pass around a pointer to an array slot and treat it like any other ref,
because the ref must be updated based on the relocation of the underlying array.
Thus the storage layout for an array slot must be the same as the storage
layout for function arguments.

Note that there remain a few special cases for which is it possible
to optimize:

 #. Arrays allocated in a non-copying region do not need to worry about
    updates to derived pointers, and can thus save one memory allocation
    per slot.
 #. Single-variant types (especially tuples) can store one metadata pointer
    for every array slot.

Whether either of these optimizations matter in practice remains to be seen.
I think a more promising route lies in converting arrays-of-tuples to
tuples-of-arrays for data parallelism.


Primitive Operations
--------------------

Having an interepeted implementation has been useful to keep the language design
"honest" about the semantics, avoiding puns particular to a single implementation.

For example, the interpreter is very clear that (to be updateable) array slots
must be store locations. The question then is: does array subscripting produce
an explicit location, modifiable via the standard assignment primitive, or do
the operations render the store location implicit?

Here the LLVM side has an answer: the correct choice is implicit.
The primary reason is that array slots are, at the GC level, derived pointers.
Avoiding casual creation of derived pointers is an obvious design choice.
Furthermore, having explicit separate operations for reading and writing
array slots also provides a nice hook for separate read and write barriers,
such as for implementing card marking.
Finally, it saves a "superfluous" deref at the source level for array reads.

Put another way, array locations are not first-class
because that would imply that instead of every ref being just a pointer,
refs created as a result of array subscripting would have to be represented
differently, as an array slice (for the GC to know what updated slot value
to write). Thus we'd either need different layout
``(pointer to slot, array pointer)``
or different operations ``(pointer to (pointer to slot, array pointer))``.
The same reasoning applies to slots of data structures.

Disciple bites the bullet and provides a ``#`` operator;
``a#b`` is like ``&(a.b)`` except that it produces a ref which internally
embeds a pointer to the parent object.

Types
-----

Musings::

  Array n T ::              Type
  Array n ::      { Type -> Type }
  Array :: { Nat -> Type -> Type }

  Array :: { {n:Int | n > 0} -> Type -> Type }


  DArray :: { Type -> Type }
  $DArray T ::       Type


  newArray :: { (a:Type) -> (n:Nat) -> {Nat -> a} -> Array n a }
  newDArray :: { (a:Type) -> Int -> {Int -> a} -> DArray a }
