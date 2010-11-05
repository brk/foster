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

Used As  Storage/     Passed As  Comments
         Stack Slot

=======  ==========   =========  ==============================
i32      (i32)/N/A    i32        SSA immutable val
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
* Actually, the double-pointer stack slot is only for consistency
  in Clang's generated code. There is no operator available to
  mutate the pointer in the stack slot independently of the object
  it points to.

.. note::

  The simplest approach for now is to use Java semantics
  and have variables of type ``T`` live in stack slots of type ``T*``.
  Since most variables will refer to (lowered) pointer types,
  the net effect is to have a type U map to a ``L(U)*`` stored
  in a stack slot of type ``L(U)**``.

Just to be explicit, here are the possibilities
for a pointer to some structure S:

=======  ==========   =========  ==============================

Used As  Storage/     Passed As  Comments
         Stack Slot

=======  ==========   =========  ==============================
 S*       (S* )/N/A     S*        SSA immutable val
 S*       S**          S*        locally-mutable vars
 S*       S***         S**       C++-style non-const reference
=======  ==========   =========  ==============================

Pointers and References
-----------------------

Given parameters
  * ``int x`` with a stack slot of type ``i32*``
  * ``int* p`` with a stack slot of type ``i32**``, and
  * ``int& r`` with a stack slot of type ``i32**``

The following snippets of C correspond to the following loads and stores:

``x = 1;``
    ``store 1 in x_addr``
``p = &x;``
    ``store x_addr in p_addr``
``r = x + 2;``
    ``store deref(x_addr) + 2 in deref(r_addr)``
``x = r + 1;``
    ``store deref(deref(r_addr)) = 1 in x_addr``
``*p = 3;``
    ``store 3 in deref(p_addr)``
``p = &r``
    ``store deref(r_addr) in p_addr``

.. store :: T -> T* -> ()
.. load  :: T* -> T

======  =============  ====================

Expr    LHS            RHS

======  =============  ====================
``x``   x_addr         deref(x_addr)
``p``   p_addr         deref(p_addr)
``r``   deref(r_addr)  deref(deref(r_addr))
``*p``  deref(p_addr)  deref(deref(p_addr))
``&x``  N/A            x_addr
``&p``  N/A            p_addr
``&r``  N/A            deref(r_addr)
======  =============  ====================

Note that the expression ``r`` is equivalent to ``*p``.

A variable ``x`` denotes the contents of a
location in memory. It is represented as an address,
implicitly dereferenced when used in an expression,
except in the LHS of an assignment.

``&x`` yields the address value of a variable.

A mutable pointer ``p`` is a variable that happens to
contain a location value. On the RHS, ``*p`` yields the
value pointed to by the contents of the ``p`` variable.
On the LHS, ``p`` refers to location value stored in ``p``.

A reference is equivalent to a pointer that is
dereferenced at every mention, with one exception

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

One issue that I haven't yet come to any conclusion about is stack overflow.
An obvious baseline is that stack overflow cannot compromise safety.

But does every function call have to check for stack overflow?
Can such checks be elided in common cases?
What can static analysis do to eliminate stack bounds checks?

The temptation of including coroutines in the language means that
we cannot ignore the issue for long.

Ideally, coroutines would be "pay-as-you-go" in terms of stack cost.
That is, the space allocated for a coroutine should be at most a
constant factor greater than the space the coroutine has needed.
The alternative is to preallocate, for each coroutine, a stack large enough
to hold the coroutine's activation frames.

The problem is that allocating small initial stacks for coroutines
forces the issue of stack overflow.

In order to avoid stack overflow, functions must check their stack pointer
relative to the allocated bounds. In a CPS-based system, this check implicitly
occurs when allocating a new activation frame on the heap, and functions
only begin executing once they have been guaranteed sufficient space.
Otherwise, function prologues must explicitly check for stack overflow.

Go is not CPS, but it does use heap-allocated stacks, organized as
a linked list. Every function prologue spends ~3 instructions comparing
the stack pointer to the bounds of the function's stack allocation, and
calls ``morestack()`` (which, eventually, calls ``gcmalloc()``) if it needs
more stack.

See http://golang.org/src/pkg/runtime/proc.c
and http://golang.org/src/pkg/runtime/386/asm.s

Possible techniques for coroutine stack handling:

* Non-resizable stacks
* Resizable stacks
 * Stack chaining with non-contiguous stacks
 * Stack slicing with contiguous stacks
 * Reallocation with contiguous stacks

One subtle consequence of using a straightforward implementation of stack
chaining is that the effective stack depth becomes limited by the size of
the heap, which is presumably much larger than the limits imposed by a
regularly-sized stack. The net effect (in a language that already has
loops and/or TCO) is that unexpected non-tail recursion manifests as
slowdown from virtual memory thrashing rather than a simple SO exception.

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

Garbage Collection
------------------

GC Maps
^^^^^^^

A standard object GC map specifies the offset of all pointers within an
object (and possibly their types, if statically known).

The GC must know how large an object is in order to

1. copy it
2. advance to the next object

For arrays, only the used portion must be copied, though the entire portion
may be copied. Advancing to the next object requires knowing the allocated size.

Objects which are not allocated in a moving heap are not subject to the
copying restriction, and may or may not be subject to the total-size
restriction.

If an array containing pointers is mutated, the mutated segment should be
marked (with a scheme such as card marking) to ensure that no
inter-generational pointers are lost, and also that writes have
bounded cost, never O(n) cost.


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
