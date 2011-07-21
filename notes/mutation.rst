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


