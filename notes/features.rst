Motivation for Features
=======================

Overloading
-----------

In the C family, when the type checker sees a variable being mentioned,
the variable's type is known with as much precision as it will "ever" be.
Therefore, the type checker can use the specific known type to permit
overloading. Furthermore, trivial instances of overloading (such as using ``+``
for int and float addition) can be statically resolved to distinct code
sequences.

With inferred types, however, overloading is not so simple, since the use
of a variable with as as-yet-not-fixed type can only generate a constraint
to be later resolved. Thus OCaml has both ``+`` and ``+.`` for int and float
addition, so that generated constraints can be for a specific type, rather
than a more-difficult-to-handle set of types. Haskell, meanwhile, requires
that each overloaded symbol be present in at most one globally-unique
type class. Thus, given an overloaded symbol like ``+``, a Haskell type checker
can look up **the** type class associated with ``+`` (that is, ``Num``), and
generate a constraint that the args to ``+`` are instances of ``Num``.

Another reflection of the differing philosophies lies with record field names.
What does the type checker do when it sees a record field lookup ``v.f``?
In Haskell, record fields are functions from the record type to the field type.
In order to support type inference, field names must be unique across all
record types in a module. In practice, this means that the name of the record
type is usually encoded in the name of the field. In contrast, in the C
family, a field lookup ``v.f`` is always checked in an environment
where the type of ``v`` is known, and thus the type of ``v.f`` can be
synthesized by inspecting the type of ``v``.


Type Inference
--------------

Type inference is great for "small" examples,
where types are obvious by inspection.

At the same time, explicitly documenting the types of top-level functions
is (almost?) universally considered good style in Haskell. Doing so
has a number of benefits:

* Explicit type annotations aid human readers follow what a function does.
* Explicit type annotations let the compiler give much better error
  messages for a category of problems which are not caught by
  type inference alone, namely, well-typed definitions that
  happen to have a type other than what the author expected.

Damas-Milner style type inference (that is to say, complete type inference
of un-annotated programs) breaks down in the presence of
fancier type systems than Hindley-Milner. Impredicative polymorphism,
subtyping, and refinement types tend to lead to intractable and/or
undecidable reconstruction problems.


Therefore, we would like to strongly encourage explicit annotations
on top-level function definitions. This could be done via syntactic
choices or via tool support (e.g. Haskell gives warnings, with inferred
types, for top-level declarations without explicit annotations).

Within a function, meanwhile, we could use either standard HM inference
a bidirectional approach for inferring the structure of types.
Inferring effects requires global propagation, because effects are constrained
by inequalities, not equalities.

Integers
--------

John Regehr has written about integers in programming languages a few times:
https://blog.regehr.org/archives/641 and https://blog.regehr.org/archives/642

There are a few choices he outlines:

 #. undefined overflow semantics: enables some optimizations (which ones?),
    but not a feasible option in a safe language
 #. two's complement overflow semantics: reasonably efficient, kills some
    optimzation opportunities; biggest flaw is that overflowed results are
    usually very far from mathematically accurate result
 #. forbid overflow by dynamically extending precision (bignums); downside is
    that computing correct results may require allocation.
 #. forbid overflow by dynamically trapping when an imprecise result would be
    calculated (as-if-infinitely-ranged)
 #. forbid overflow by statically analyzing integer ranges and only allowing
    operations that can be proven not to overflow.
 #. reduce instances of overflow by using larger fixed-precision types.

I actually don't think #4 (the AIR model) makes a lot of sense; for domains
where allocation is unacceptable, wouldn't trapping also be unacceptable?
If you can't handle either, that just leaves static analysis or explicit wraparound.


Robustness
----------

    Because of [Modula-3]'s requirements on name qualification and method overriding, it is impossible to break a working program simply by adding new declarations to an interface (any interface).
    - http://en.wikipedia.org/wiki/Modula-3


.. An interactive code sample::
..
..   >>> 1 + 1
..   2
..
.. A non-interactive code sample:
..
.. .. code-block:: haskell
..
..   Y f = f (Y f)
..
.. A shell example:
..
.. .. code-block:: bash
..
..   $ ccmake ../foster
..
.. Cool, eh?
..
.. Built |today|.
