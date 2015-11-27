Integer Behavior
================

Hardware provides fixed-width arithmetic. Unfortunately, machine arithmetic
operations are partial due to preconditions (for division/modulus, shifts)
and the possibility of overflow (for most operations).

There are, broadly, several ways of handling this situation::
  * "The C approach": declare the special cases to be undefined behavior.
  * "The Java approach": signed overflow behaves as two's complement; other precondition violations handled with exceptions.
  * "The Python approach": handle overflow by promoting to bignums, and precondition violations with exceptions.

Other possibilities:
  * Use saturating instead of wrapping arithmetic; both are sometimes useful, but neither provides the mathematically-correct result.
  * Make potentially-overflowing operations perform dynamic checks to detect overflow.
  * Eliminate overflow by producing double-width results
     - "Overflow" checks then become dynamically-checked non-lossy truncations,
       which are a useful primitive in their own right.
     - However, they would almost always need to be used in combination in real code, I think...
     - Unlike with Python, there is still a distinction between differently-sized integer types.
  * Perform static checks to eliminate edge cases
     - Is this really feasible? What languages have tried this?

Fixnum Issues
=============

Taking the requirement of exposing sized integer types as a given, how should they be handled?
The approach in C goes roughly like this:
  * Use a family of types for representing signed and unsigned integers of different (but unspecified) bitwidths.
  * Use subtyping and coercion rules to invisibly insert extensions and truncations where needed.
  * Use overloading to avoid having distinct operations for primitives on different sizes.

Java is similar, except that unsigned types are not included, and overflow behavior is defined.

Haskell uses type classes to avoid distinct operations for the sized primitives, and implicitly coerces
literals (but not arbitrary expressions) using ``fromIntegral``. Haskell also boxes its sized integer types,
since the language doesn't directly expose the difference between boxed and unboxed types.

TODO review the Habit paper and its treatment of sized integer types & type classes.
  
.. [1] http://trac.sacrideo.us/wg/wiki/NumericTower
.. [2] http://www.ccs.neu.edu/home/stamourv/papers/numeric-tower.pdf
.. [3] http://www.ccs.northeastern.edu/racket/pubs/icfp10-thf.pdf


.. http://www.it.uu.se/research/group/hipe/papers/succ_types.pdf

.. Tag Elimination, or, Type Specialisation is a Type-Indexed Effect
..        http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.101.2805&rep=rep1&type=pdf
.. Formally Optimal Boxing
..
