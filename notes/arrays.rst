Arrays
======

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

  Array :: { {n:Int | n >= 0} -> Type -> Type }


  DArray :: { Type -> Type }
  $DArray T ::       Type


  newArray :: { (a:Type) -> (n:Nat) -> {Nat -> a} -> Array n a }
  newDArray :: { (a:Type) -> Int -> {Int -> a} -> DArray a }




  PrimMutableDArray :: Type -> Type
  newDArrayPrim :: { (a:Type) -> Int -> { Int -> a } -> PrimMutableDArray a }
  getDArraySlot :: PrimMutableDArray T -> Int -> T
  setDArraySlot :: PrimMutableDArray T -> Int -> T -> ()


  MutableArray
  mutableArrayCap :: MutableArray T -> Int
  mutableArrayLen :: MutableArray T -> Int
  mutableArrayAppend :: (in: MutableArray T)
                     -> T
                     -> (out:MutableArray T|len in + 1 == len out)

A key point is whether the same read operation is permitted to read from both
mutable and immutable arrays. Since they share a representation, this should
be permissible. Likewise, should the same dereference operation work on both
heap and stack slots?

Array mutability polymorphism seems attractive.
The obvious case is functions which (directly or indirectly) poke the array,
and thus must take a mutable array argument.
The remaining functions can be divided into two cases: those which require
that their argument not be mutable (not even by someone else), and those which,
at least at first glance, are truly agnostic to the mutability of their array
argument. An example of an agnostic function would be array iteration.
An example of a non-agnostic function would be a constructor for an immutable
bignum -- not only will the bignum module not mutate the array it is given,
it cannot protect its semantics if other functions can mutate the array out from
underneath it.

If immutable arrays and immutable arrays get different types, then avoiding
code duplication for agnostic functions is harder. (One solution might be
something like an IndexableSeq typeclass, rather than using array directly).
A bigger problem is avoiding mutability contamination. Because functions like
``arrayFromRange32`` are implemented using local mutation of a fresh array,
they must return mutable arrays, even though the client is free to (safely)
treat the returned value as an immutable array.

An alternative is to use a single type constructor for mutable and immutable
arrays, with kind ``Region -> Type -> Type``. Then agnostic functions can be
parametrically polymorphic over the region, and non-agnostic functions can use
some unspecific means applying region and/or effect constraints. This captures
the idea that the representation of mutable & immutable arrays is the same.

The region-based approach also more easily integrates ST-style array freezing.

-------------------


Translating LLVM to a functional language:
  * Basic blocks (with phi nodes) become functions (with arguments).
  * Branches become function calls; values identified in phis are the actual params.
  * No need to worry about returns in non-tail positions!
  * Primops get translated as-is.
  * Problems:
    * Calls to primitives
    * "Undoing" GC slots, object initialization, etc.
    * Handling stack allocations
    * Handling unsafe memory idioms



