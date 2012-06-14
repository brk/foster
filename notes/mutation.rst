Mutation
========

Basic data model::

          data Example = C { v : Int32 ; e : Example }
                       | N { v : Int32 }


          [ C | * | 1 ]     [ N | 2 ]
              ^  +------>------^
              |                |
          +---+            +---+
          |                |
        [ h ]            [ t ]

        t = N 2
        h = C 1 t

 -------------------------------------------------------------------------------

        h := N 3     -- allocates, only overwrites the variable

          [ C | * | 1 ]     [ N | 2 ]
                 +------>------^
                               |
          +--->[ N | 3 ]   +---+
          |                |
        [ h ]            [ t ]


 -------------------------------------------------------------------------------

        h #= N 5      -- Does not need to allocate, overwrites existing memory.
                      -- Note that this implies that the size of every leg
                      --   is the max of the size of any leg, i.e. we may waste
                      --   some memory in some circumstances.

          [ N | 5 |.1.]    [ N | 2 ]
              ^                ^
              |                |
          +---+            +---+
          |                |
        [ h ]            [ t ]

 -------------------------------------------------------------------------------

        h.e.v := 5   (or #= 5... same semantics for unboxed types)

          [ C | * | 1 ]     [ N | 5 ]
              ^  +------>------^
              |                |
          +---+            +---+
          |                |
        [ h ]            [ t ]

 -------------------------------------------------------------------------------

The above model is very flexible, but there are a few unresolved questions
about it:

1) What are the language's l-values?
        Let-bound variables? Pattern-bound variables? Return values from
        functions? Array slots?
2) How do the available forms of mutation interact with pattern matching
   semantics? In particular, are fields bound by pattern matching lvalues?
   Are scrutinzed objects subject to mutation?
3) What optimizations do different forms of mutation prohibit or permit?
4) What restrictions (if any) should be placed on mutation?
        For example, maybe single-constructor datatypes should be treated
        specially?

        
Representation: pointer tagging
===============================

If an object in memory is potentially aliased, AND we want to update its tag,
then its tag must be on the object, not on the pointers to the object.

But if we know that a given object has only one alias,
or we don't ever need to update its tag,
then we can tag the pointer(s) rather than the object itself.

This implies that immutability brings locality benefits,
because we don't need to peek through the pointer to match the tag!

Mutability And Algebraic Data Types
===================================

* ``h.n.v`` syntax only makes sense if the types of h and n guarantee the
  presence of n and v fields. This leaves a choice of two alternatives:
    1) Require that there is only one leg in the union, or generalize to:
    2) Require that every leg of the union provide the same field with the same
       layout at the same offset position.

Other thoughts
==============

* Having the compiler convert Array-of-Tuples to Tuple-of-Arrays is a very desirable optimization.


Garbage Collection
==================

With copying GC, it's illegal to keep a bare pointer to a field live across a
potential GC point, because the field address is derived from the object's base
address, which must be assumed to move.

So mutable struct fields, pattern matching, and copying GC lead to an
interesting interaction. Suppose we have some code::

       // suppose t = (x,p@(y,z))                            /---> [ x | p ]
       case t of                                             |           |
         (a, (b, c)) -> foo(c);           t_addr [ t *-]-----/  +--------+
                        gc();                                   |
                        c := 4                                  +->[ y | z ]
       end

Now, what exactly do we bind to ``c`` in the body of the match?

If we bind the address of ``z``, we will have a stale value after the GC cycle.
We could keep a pair of ``p`` and an int offset, but this is pretty ugly, and it
penalizes readers to benefit writers -- probably not the right tradeoff.
... ??? also loses out on LLVM's type safety: GEPs on structs are restricted to
statically-known offset, so we'd be forced to fall back on raw ptr arithmetic.

Potential solutions:

* Keep ``p`` as a stack root (so it will be updated by the GC) and recompute
  ``z_addr = &p[1]`` after each safe point. With ``n`` live mutable addresses
  bound at depth ``k``, this implies ``n * k`` loads after every safe point.
  This is bad in the general case, but due to programming style, I'd expect
  that ``n`` is likely to be small and ``k`` will probably be ``1``.
  And if there are no safe points in the scope of the bound addresses,
  there will be no reloads, either...

* Disallow mutable fields; force all mutability to go through (implicit or
  explicit) references. Then we can copy the value z to a new stack slot
  (potentially a GC root if z is a pointer), secure in the knowledge that
  the heap and stack copies of z will not go out of sync.
  One potentially negative consequence is that lazy thunks would need an
  otherwise-superfluous level of indirection.
  We would also want to be careful to avoid needless stack traffic.

* Store a pair of x and &x[1], and rely on the GC to maintain the derived
  pointer when the base pointer is moved. This is probably needed for a
  first-class treatment of mutable fields. The downside is that we have to
  choose between bloating conventional references to two pointers instead of
  one, or adding yet another layer of indirection, or using types to
  distinguish between tidy and untidy references.
  Intuitively, either of the first two choices would have a negative impact
  on program performance, but it is not clear what, exactly, that would be.


Boxing and Unboxed Representations
==================================

The nbody benchmark's C implementation uses the following data layout::
  
    bodies: *------>[[ b1.f1 | b1.f2 | ... ][ b2.f1 | b2.f2 | ... ]]

where structs are stored unboxed in the array, and all the fields are
mutable in-place.

Without mutability or a notion of unboxed user-defined types, we can do this::
  
    bodies: *------>[ b1 | b2 | ... ]
                      |
                      |
                      +--->[ f1 | f2 | ... ]
                      
but mutability of the fields introduces an artificial layer of indirection::
  
    bodies: *------>[ b1 | b2 | ... ]
                      |
                      |
                      +--->[ * |  * |  ... ]
                             |    |
                             |    +---> [ f2 ]
                             |
                             +-->[ f1 ]

Why is this an artificial layer of indirection?
    The ref cells are encapsulated by their container (owned, unique, whatever).
    This actually isn't strictly true: there are accessor functions which
    return the ref cell pointer, but the key is that (**after inlining**) those
    returned ref cells are always used "immediately" -- there are no long-lived
    aliases to the ref cells which would prevent the cells from being inlined
    into their parent objects.
    

