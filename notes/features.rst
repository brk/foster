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

Coroutines via libcoro
++++++++++++++++++++++

libcoro provides the following interface::

    coro_create :: { env, (env -> void) } -> coro
    coro_transfer :: { coro, coro } -> void

The semantics of ``coro_create(e, f)`` is that, when a coroutine is
first transferred to via ``coro_transfer``, the coroutine will
begin evaluating ``f(e)``.

Taking inspiration from Lua (but using symmetric coroutines, to
keep the translation simpler), we'd like to expose this functionality
at the Foster level via two primitives::

    Coro :: Type -> Type -> Type
    Coro.create :: forall a r, (a -> r) -> Coro a r
    Coro.invoke :: forall a r, { a , Coro a r } -> { r, bool }

The extra boolean flag from Coro.invoke indicates whether the coroutine
is dead. It will probably be better to use maybe types instead, but anyways...

The function provided to ``coro_create`` cannot be the LLVM lowering of
the function passed to ``Coro.create``. If we pass a closure
``h :: int -> int``, the lowering will be ``h :: {env, int} -> int``,
which has an extra unwanted parameter (and the wrong return type).
For consistency, we'll use the closure version of non-closure functions, too.
So, instead, we'll have a lowered wrapper function for each (set of) argument
type(s) ``a`` and return types ``r``:
``foster_coro_wrapper_[[a]]_[[r]] :: void* -> void``.
That function will, from the ``void*``, extract the lowered function
pointer and closure env, as well as the argument(s),
and call the function with the env and whatever arguments.

We'll also have a family of coroutine structs, which the ``void*`` arg
will be cast to::

    struct foster_coro_[[a]]_[[r]] {
        coro_context ctx;
        ?? coro_context caller; ??
        closure_func fn;
        closure_env env;
        [[a]] args;
        [[r]] retval;
    }

Then the wrapper implementation will be like::

   void foster_coro_wrapper_[[a]]_[[r]](void* f_c) {
     foster_coro_[[a]]_[[r]]* foster_coro = (foster_coro_[[a]]_[[r]]*) f_c;
     foster_coro->retval = foster_coro->fn(foster_coro->env, foster_coro->args ...);
   }

One unresolved question is whether the args will be represented in the
``foster_coro_...`` struct as an unpacked series of fields, or as a single
boxed value.

The implementation of ``Coro.create [a] [r] closure_struct``
will be something like::

    foster_coro_[[a]]_[[r]]* fcoro = memalloc(...);
    fcoro->ctx = coro_create(fcoro, foster_coro_wrapper_[[a]]_[[r]);
    fcoro->fn  = closure_struct.func;
    fcoro->env = closure_struct.env;
    return fcoro;

and the C implementation of ``Coro.invoke [a] [r] arg coro`` would be roughly::

    coro->args = arg;
    coro_transfer(_this_coro's_context, coro->ctx);
    return coro->retval;

The main piece missing is: when does ``coro->retval`` get written?
As sketched, only when the coroutine target fn returns, but it ought to
happen when "yield" is called as well. With symmetric coroutines, that
means that when a coroutine ``x`` of type ``Coro a r`` is invoked, ``x``
should be (implicitly?) given a coroutine, representing the caller,
of type ``Coro r a``. The caller's coroutine can be given "return values,"
and will provide additional "arguments" in response. This setup makes
coroutines look an awful lot like unbuffered channels,
which of course makes sense...

.. note ::
    TODO describe the interaction with impredicative polymorphism -- when will
    an n-arg Foster function be lowered to a LLVM function with one parameter,
    and when will it be lowered to something with n parameters?

Impredicative Polymorphism
--------------------------

The value restriction in ML arises (in part?) because predicative polymorphism
cannot assign the correct type to a reference to the identity function.
The correct type is ``(ref (forall a (-> a a)))`` but with stratified
polymorphism, the closest approximation is ``(forall a (ref (-> a a)))``
which allows the writer and reader of such a mutable reference to disagree.

Greg Morrisett lays out some other issues with compiling polymorphism:
http://www.eecs.harvard.edu/~greg/cs256sp2005/lec15.txt

To summarize, impredicative polymorphism is neeeded for encoding existentials,
as well as polymorphic recursion and functions like Haskell's ``runST``.
Predicative (let-) polymorphism favors runtime performance at the expense
of compilation time and program expressiveness.

I'm not entirely convinced that it's better to encode existentials with
impredicative polymorphism versus directly including strong sums in the
language. But I think the other arguments are sufficient to make full System F
strongly worth considering.

Here's (top-level) Haskellish pseudo code to illustrate some implementation
issues/decisions to be made regarding impredicative polymorphism::

    id :: forall a, (a -> a)
    id x = x

    app_f64 :: { f64 , (f64 -> f64) } -> f64
    app_f64 x f = f x

    app_gen1 :: forall a, { a , (a -> a) } -> a
    app_gen1 x f = f x

    app_gen2 :: forall b, {b , forall a, (a -> a) } -> b
    app_gen2 x f = f x

    issues :: forall a, (a -> a) -> ()
    issues uid =
    /* a */   uid [f64] 42.0
    /* b */   app_f64 42.0 (uid [f64])
    /* c */   app_gen1 [f64] 42.0 (uid [f64]])
    /* d */   app_gen2 [f64] 42.0  uid

    /* x */    id [f64] 42.0
    /* y */   app_f64 42.0 ( id [f64])
    /* z */   app_gen1 [f64] 42.0 ( id [f64]])
    /* q */   app_gen2 [f64] 42.0   id
    ) ; ()

Inside the body of ``issues``, ``uid`` is bound to an unknown function.
That implies that when ``uid`` is instantiated to (presumably) different
result types, its implementation cannot be specialized for specific types.
In other words, each argument must be passed in a general-purpose register.
So e.g. on a 32-bit machine, a 64-bit floating point arg must be boxed.

Line by line:

* ``a``: ``uid [f64]`` is uniform, so ``42.0`` must be made uniform as well,
  presumably by boxing.
* ``b``: ``42.0`` need not be made uniform when it is passed to ``app_f64``,
  but inside ``app_f64``, ``f`` is an unknown function. So now we have at least
  two choices: if we pass our uniform function as-is to ``app_f64``, then we
  are basically forced to box all parameters to all functions. Or,
  we could instead create a wrapper with type ``(f64 -> f64)``:
  ``uid_f64_wrapper unboxed_x = unbox(uid_generic(box(unboxed_x)))``.
* ``c``: We have basically the same question, but now it applies to both
  the (presumed "known") definition ``app_gen`` as well as the unknown ``uid``.
  We could specialize ``app_gen`` to take an unboxed ``x`` arg, and
  (independently) expect the function arg to take (un)boxed args.
* ``d``: This mainly highlights the extra freedom given by ``app_gen1``.
* ``x``: because we have the definition of ``id``, we can perform type
  instantiation at compile time, producing a completely specialized ``id_f64``.
* ``y``: see ``b``, only make the reverse decision...
* ``z`` and ``q``: mostly as with ``c`` and ``d``.


Polymorphic Recursion
+++++++++++++++++++++

The primary example of polymorphic recursion presented in
Purely Functional Data Structures is::

  type Seq = forall a, match
                  case Nil
                  case Zero (Seq (a,a))
                  case One a (Seq (a,a))

  cons x (One y ps) = Zero (cons (x,y) ps)

Note that calling
``cons :: int -> Seq int -> Seq int`` results in a recursive call with type
``cons :: (int, int) -> Seq (int, int) -> Seq (int, int)``

Okasaki notes that polymorphic recursion (i.e. higher-rank System F)
implies undecidable inference without type signatures. Since we expect
Foster code to have top-level type signatures, this shouldn't be an issue.

Implementation Sketch
+++++++++++++++++++++

I'd prefer to avoid "requiring" JIT compilation for security,
latency, and opportunity-cost reasons. (Using a JIT for a REPL instead of
interpreting is of course orthogonally possible).
This leaves monomorphization, uniform representation, coercions,
and intensional polymorphism. At least to start, I think the right
approach for Foster will be to simply make do with predicative polymorphism.
Having the power of full System F would be nice, but it's not a core goal
of the language, and the issues laid out by Morrisett are troubling.
In particular, the implication of uniform source types seems to be creeping
coercions or complicated type-passing schemes, and the alternative --
non-uniform source-language types -- is (perhaps) even more unpleasant.

Sadly, let-polymorphism is not the land of milk and honey, either.
See the machinations Disciple had to go through to control generalization
of "dangerous" type variables. But it's probably easier, on balance, than
coming up with a completely satisfactory solution to compiling System F.

Overloading
-----------

In the C family, when the type checker sees a variable being mentioned,
the variable's type is known with as much precision as it will "ever" be.
Therefore, the type checker can use the specific known type to permit'
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

Overall, the Haskell approach to overloading seems superior to OCaml's approach,
but the restriction to a single global type class instance for each overloaded
symbol seems troubling to me.  C++ was going in a similar direction with
concepts, though I'm not sure how the Indiana and Texas proposals handled
the C++ equivalent of the global instance restriction.

Another reflection of the differing philosophies lies with record field names.
What does the type checker do when it sees a record field lookup ``v.f``?
In Haskell, record fields are functions from the record type to the field type.
In order to support type inference, field names must be unique across all
record types in a module. In practice, this means that the name of the record
type is usually encoded in the name of the field. In contrast, in the C
family, a field lookup ``v.f`` is always checked in an environment
where the type of ``v`` is known, and thus the type of ``v.f`` can be
synthesized by inspecting the type of ``v``.


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
