Arrays
======

Allowing arrays as global variables permits much easier translation of some
C code, but doing so is only safe if those arrays are immutable.

Of course, mutable arrays are a necessity in certain circumstances.
And sometimes, we want to mutably initialize an array and then treat it
as immutable afterwards.

Finally, the common case for arrays is dynamically-known length,
but it's very nice to also allow arrays with fixed, statically-known length.

So as I see it, the three big questions with a simple array design are
providing support for:
* mutability
* static sizing
* freezing



There are of course higher-level concerns, such as casting/aliasing certain
types of primitive arrays, as well as APL/J-style rank typing and
DPJ-style deterministic parallelism.

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
the idea that mutable & immutable arrays share the same representation.

The region-based approach also more easily integrates ST-style array freezing.

A somewhat hacky alternative to ST-style array freezing is to dynamically
freeze arrays. Regardless of whether mutable and immutable arrays have separate
types, a primitive can be provided which takes a mutable array and returns an
immutable array. With ST, the escaping-type-variable check ensures that the
returned array cannot escape the scope of the run function. Type system support
(e.g. for affine types) can ensure that no aliases of the mutable array exist,
leaving array freezing as a special case of sound strong update. Without such
support from the type system, we can still do the transmutation -- but at two
costs. First, we must ensure that aliases of the mutable array are rendered
impotent; without static support, that basically means marking the array value
at runtime, which in turn implies that some operations on mutable arrays can
fail for "spurious" reasons. Subtle knock-on effects include the difficulty
of hoisting array-mutability checks out of loops, since anything that might call
the array freeze function could "invalidate" an existing mutable array. The second
cost is that type-based alias analysis must be slightly weakened, as it is now
possible for an immutable array to be aliased with a mutable array. On the other
hand, whenever a mutable array must-alias with an immutable array, the mutable
alias would not be modifiable at runtime.
