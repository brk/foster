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

        h = [1, 2]
        t = [2]

 -------------------------------------------------------------------------------

        h := [3, 4]     -- allocates, only overwrites the variable

          [ C | * | 1 ]     [ N | 2 ]
              ^  +------>------^
              |                |
          +---+            +---+
          |                |
        [ h ]            [ t ]

        h = [1, 2]
        t = [2]

 -------------------------------------------------------------------------------

        h #= [5]

          [ N | 5 ]     [ N | 2 ]
              ^                ^
              |                |
          +---+            +---+
          |                |
        [ h ]            [ t ]

        h = [5]
        t = [2]

 -------------------------------------------------------------------------------

        h.e.v := 5

          [ C | * | 1 ]     [ N | 5 ]
              ^  +------>------^
              |                |
          +---+            +---+
          |                |
        [ h ]            [ t ]

        h = [1, 5]
        t = [5]

Is r tagged? Can T2 be updated?
If an object in memory is potentially aliased, AND we want to update its tag,
then its tag must be on the object, not on the pointers to the object.

But if we know that a given object has only one alias, or we don't ever need to update its tag,
then we can tag the pointer(s) rather than the object itself.

This implies that immutability brings locality benefits, because we don't need to peek through the pointer to match the tag!


* Having the compiler convert Array-of-Tuples to Tuple-of-Arrays is a very desirable optimization.

* ``h.n.v`` syntax only makes sense if the types of h and n guarantee the presence of n and v fields, which fundamentally means there is only
  one leg in the union (ignoring layout issues...).



With copying GC, it's illegal to keep a reference to a field across a potential
GC point. So mutable struct fields, pattern matching, and copying GC lead to an
interesting interaction. Suppose we have some code::

       // suppose t = (x,(y,z))                              /---> [ w | x ]
       case t of                                             |           |
         (a, (b, c)) -> foo(c);           t_addr [ t *-]-----/  +--------+
                        gc();                                   |
                        c <- 4                                  +->[ y | z ]
       end

Now, what exactly do we bind to c in the body of the match?
If we bind the address of z, we will have a stale value after the GC cycle.
We could keep a pair of x and an int offset, but this is pretty ugly, and it
also loses out on LLVM's type safety: GEPs on structs are restricted to
statically-known offset, so we'd be forced to fall back on raw ptr arithmetic.

Potential solutions:

* Recompute z_addr = &x[1] after each safe point. With n live values bound
  at depth k, this implies n*k loads after every safe point.

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


