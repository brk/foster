Motivation for Features
=======================

LLVM Lowerings
--------------

LLVM enforces a distinction between objects, which live in memory
and can be mutated via ``store`` instructions,
and values, which are single-assignment (i.e. not mutable)
and live in registers.

LLVM provides a highly effective optimization pass called ``mem2reg``,
which takes values stored on the stack (in memory) and promotes them
to registers. The ``mem2reg`` pass is used for all function-local variables
in llvm-gcc and clang.

There are three different ways in which a source-level variable
could be lowered to LLVM IR, which correspond to different semantics
for the variable. Possible representations for a variable of type
i32, which generalizes to any type T:

=======  ==========   =========  ==============================

Used As  Stack Slot   Passed As  Comments

=======  ==========   =========  ==============================
i32      N/A          i32        SSA immutable val
i32      i32*         i32        locally-mutable vars
i32      i32**        i32*       C++-style non-const reference
=======  ==========   =========  ==============================

Other combinations are possible, but those are the most
obviously useful. A few items of note:


* The clang frontend emits only the locally-mutable var
  and non-const reference lowerings. The first row of the table
  is handled by ``mem2reg``.

* Java semantics (pass reference by value) can be handled
  entirely by locally-mutable vars.

* C# or C++-style reference semantics could be implemented using
  the third technique; it remains to be seen whether
  reference semantics are actually needed or not.

.. note::

  The simplest approach for now is to use Java semantics
  and have variables of type T live in stack slots of type T*.
  Since most variables will refer to (lowered) pointer types,
  the net effect is to have a type U map to a L(U)* stored
  in a stack slot of type L(U)**.

Parameter Passing
-----------------

When is it safe and profitable to pass params by value
instead of by (const or non-const) reference?

* Value size known and fixed, type is not opaque reference.
* Value size is <= n machine words, for some small n.
  SIMD vectors are an exception, since they have dedicated
  machine registers which are larger than one regular word.
* The ref must not be written through
  (but it can be rebound).
* Copying must be defined for the type. The primitive types
  are trivially and implicitly copyable, but copying is not
  well defined for all types.

Pass-by-val reduces derefs across function boundaries,
and may or may not free up machine registers. Stack
allocation has primary savings from reduced gc
pressure/collection costs.

In a system which tracks ownership, values owned by the
current function may be inlined (i.e. stack allocated)
if they are not too large.

With the Cardelli optimization, it may be marginally
more efficient to pass some ADTs by (tagged?) pointer
than strictly by value.  But that's a very small
optimization, I think.

.. note::
        The question of pass-by-ref vs pass-by-val is
        *orthogonal* to the question of whether
        allocation happens via alloca or via gcmalloc!

Unboxing and Inlining
---------------------

The high-level semantics of Foster is that every object is
represented as a (possibly mutable) pointer, roughly like
Java. I aim to follow the DDC model of inferring and
representing mutability as constraints on locations, rather
than as magical type pseudo-constructors as in BitC.
I'm not sure offhand whether type qualifiers are a good
approach for dealing with mutability constraints.

Unlike Java, Foster seeks to provide a means to let
programmers guide object inlining, in both stack frames and
in heap allocated objects.

Inlining (of code and data) is great in that it reduces
indirection costs, which includes pointer dereferences, page
faults, and GC overhead in time and space.

The cost is that inlining implies tighter dependencies and
loss of encapsulation.  If module A uses inline functions
and/or objects from module B, then A must be recompiled when
B changes its implementation, even if B does not change its
logical interface.

An extra restriction on unboxing function parameters is that
copying must be defined. Unboxed object slots may or may not
require default constructability.

The current plan is to have inlining be controllable by
a combination of ownership rules (inferred) and distinction of
"strong" vs regular imports (not inferred). I want to
explicitly avoid introducing an "unboxed" or "inlined"
annotation, because it clutters code with information that is
almost never semantically relevant.

Coroutines
----------

Impredicative Polymorphism
--------------------------

Overloading
-----------

Effects
-------

Regions
-------

Types
-----

Type Inference
--------------

Type inference is great for "small" examples,
where types are obvious by inspection.

At the same time, explicitly documenting the types of top-level functions
is (almost?) universally considered good style in Haskell, Doing so
has a number of benefits:

* Explicit type annotations aid human readers follow what a function does.
* Explicit type annotations let the compiler give much better error
  messages for a category of problems which are not caught by
  type inference alone, namely, well-typed definitions that
  happen to have a type other than what the author expected.

Damas-Milner style type inference (that is to say, complete type inference
of un-annotated programs) breaks down in the presence of
fancier type systems than Hindley-Milner. Impredicative polymorphism,
subtyping, and higher-rank types tend to lead to intractable and/or
undecidable reconstruction problems.


Therefore, we would like to strongly encourage explicit annotations
on top-level function definitions. This could be done via syntactic
choices or via tool support (e.g. Haskell gives warnings, with inferred
types, for top-level declarations without explicit annotations).

.. todo::
	Think and write more about syntax for type annotations.

Within a function, meanwhile, we could use either standard HM inference
a bidirectional approach for inferring the structure of types.
Inferring effects requires global propagation, because effects are constrained
by inequalities, not equalities.


Dependent Types
---------------

ADTs
----

Records
-------

Named Parameters
----------------


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
