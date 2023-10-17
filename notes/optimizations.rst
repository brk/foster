A Code-Size Optimization
------------------------

Because data constructors are (relatively) heavyweight,
we can save code size in some cases by merging continuations::

        foo2 = { i : Int32 =>
          if i <Int32 0
            then IntInf (natFromInt32 (0 -Int32 i)) True
            else IntInf (natFromInt32 i)           False
          end
        };

        foo3 = { i : Int32 =>
          case (if i <Int32 0 then (0 -Int32 i, True)
                              else (         i,False))
           of (x, b) -> IntInf (natFromInt32 x b)
          end
        };

This optimization makes more sense for ctors than general calls
because

* ctors can't be usefully specialized for known arg values,
  whereas some calls to known functions can be specialized.
* a ctor call is relatively many insns; a call is just one.

I believe this optimization is not (yet) implemented by the Foster compiler.

Inlining, Specificially
-----------------------

As described in [1] and [2], the primary means of optimizing a functional program
is beta reduction (that is: compile-time partial evaluation). The primary benefit
in practice is avoiding allocation of function closures, by turning code like
``f = { x => x + 1 }; f y`` into ``y + 1``. (The elimination of the indirect
function call itself is a minor benefit, but generally pales in comparison to the
cumulative effect of allocation in a loop.)

When applied without care, inlining leads to potentially-exponential code blowup.
The core of the problem is that code like ``f = { ... }; f !; f !;``
inlines to ``... ; ...``, which may get duplicated in turn.

Variants of inlining which are guaranteed to not cause code blowup are called *shrinking*
optimizations. Appel & Jim show that (a given set of) shrinking optimizations are confluent
(meaning they can be applied in any order and converge on the same final optimized program).

The standard way of shrinking in a functional compiler is to start with an immutable AST,
and then iterate a "shrinking step" function, which first gathers *census* information and
then uses it to apply those optimizations which the census shows to be safe.
(A census is a tally of variable occurrence counts,
for determining which inlinings will not lead to code blowup, and which bindings may be dropped.)
Iteration is needed because the census becomes inaccurate as inlinings are applied,
resuling in missed simplifications.

The problem in turn is that no constant bound on the number of iterations suffices.
In the worst case, a linear number of passes are needed, making simplification possibly
quadratic in program size. To avoid this slowdown, iteration may be halted before all simplifications
have been performed. Appel & Jim note that carefully updating the census can lead to faster
convergence of the algorithm in practice, but does not change the asympototic limits or tradeoffs.

To recap: in a mutation-free setting, shrinking may be either linear time or exhaustive,
but (at least as far as the known state of the art) not both. However, by using in-place mutation,
the census can be directly "read off" variable bindings and occurrences, and exhaustive shrinking
can be performed in linear time. Appel & Jim describe but do not implement such an algorithm.

Benton, Kennedy, and Russell implement a variant of the census-updating algorithm in their MLj
compiler [3]. They report that, while each simplification pass is fast, repeated application
results in simplification taking roughly half of total compilation time.

Kennedy [1] presents (and implements) an improvement to Appel & Jim's un-implemented mutable/graphical
scheme. Kenedy uses imperative union-find to obtain effectively-linear exhaustive simplification.
I have re-implemented his algorithm in ``MKNExpr.hs``.

Waddell and Dybvig [4] present a linear-time (but incomplete) algorithm for general, unrestricted
beta reduction interleaved with constant propagation. This approach has several desriable properties
(online, polyvariant, context-sensitive, demand-driven). A variant of this algorithm was once
implemented in ``KNExpr.hs`` but I found it to be... temperamental.


#. `Compiling with Continuations, Continued <http://research.microsoft.com/en-us/um/people/akenn/sml/CompilingWithContinuationsContinued.pdf>`_
#. `Shrinking Lambda Expressions in Linear Time <http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.55.7347&rep=rep1&type=pdf>`_
#. `Compiling Standard ML to Java Bytecodes <http://research-srv.microsoft.com/en-us/um/people/nick/icfp98.pdf>`_
#. `Fast and Effective Procedure Inlining <http://www.cs.indiana.edu/~dyb/pubs/inlining.pdf>`_


GC Optimizations
~~~~~~~~~~~~~~~~

In years past, the Foster compiler implemented dataflow-driven optimizations of GC roots,
both to eliminiate unnecessary uses of GC roots as well as to merge roots with disjoint
lifetimes (thereby shrinking activation record sizes).

Currently, we avoid the issue entirely by treating the stack conservatively, which
obviates the need for GC roots.

Data Structure Elimination
~~~~~~~~~~~~~~~~~~~~~~~~~~

The following idioms should not involve runtime allocation::

        case (x1, ..., xn) of ... end

        let v = (x1, ..., xn) in case v of ... end end

We can also generalize this in a few ways.
This can also work for any single-constructor datatype, not just tuples.

Status: implemented; pattern matching on tuple literals does not allocate.
I believe that the same optimization also applies in the general
ADT case but have not checked recently.


Furthermore, it doesn't really require a single-ctor type, either;
as long as the head constructor of the scrutinee is known,
we can statically prune the decision tree to eliminate impossible cases.
For example::

        case  B x1 ... xn
          of $A ...
          of $B c1 ... pn
          of $B p1 ... pn
          of $C ...
        end

can be treated the same as::

        case (x1 ... xn)
          of (c1 ... pn)
          of (p1 ... pn)
        end

This is *almost* a simple case of inline substitution of subterms
for scrutinee occurrences, combined with dead-code elimination to
get rid of the possibly-unnecessary heap allocation. The subtlety
is the we also want to involve some code motion in the case where
the allocation is not eliminated::
 
        let p = (v, w) in
        case p of (C, d) -> ... use d ...
               of pair   -> ... use pair ...

should become:: 

        case v,w of (C, d) -> ... use d ...
                 of _      -> let p = (v, w) in
                            ... use pair ...

rather than::

        let p = (v, w) in
        case p of (C, d) -> ... use d ...
               of pair   -> ... use pair ...

Status: not yet implemented. I am curious about
how often such an optimization would actually apply.

Load merging
~~~~~~~~~~~~

Foster used to implement a custom LLVM optimization to detect and merge
piecewise loads + shifts + ors, based on http://blog.regehr.org/archives/959

LLVM later implemented a more complete/exhaustive version of this optimization,
so ours was removed.

At the time I observed that standard compiler optimizations could interfere
with my implementation by detecting "redundant" loads and eliminating them,
thereby turning 4 coalescable loads into 3 non-coalescable loads.
I don't know offhand if LLVM's implementation suffers from the same interference.


Pipe Operator
~~~~~~~~~~~~~

The Foster compiler implements the pipe operator (``|>``) as a built-in macro,
rearranging ASTs during parsing.

The pipe operator::

    b |> bytesDrop todrop

is syntax for::

    (     bytesDrop todrop  b   )
    (NOT (bytesDrop todrop) b  !)

Multiple pipes are treated like so::

    (b |> bytesDrop todrop |> bytesTake reslen)
    =~=
    (b |> bytesDrop todrop) |> bytesTake reslen
    =~=
    bytesTake reslen (b |> bytesDrop todrop)
    =~=
    bytesTake reslen (bytesDrop todrop b)
    

Also, if the RHS is a variable, it is treated as a function call::

    b |> f |> g  === g (f b)

Thunk invocations are special cased::

    b |> t !     === (t !) b

rather than ``t b``, because the latter can be written ``b |> t``.

This means that if we wanted e.g.::

    (bytesDrop todrop) b

instead of::

    (bytesDrop todrop b)

we can write either::

     b |> { bytesDrop todrop } !

or::

     x = bytesDrop todrop; b |> x

So currying isn't super smooth, and it's always a bit sad to
forgo first-class composition operators, but it's low-overhead,
and it seems easier to reliably reason about allocation
behavior this way, compared to the alternative of defaulting
to curried application with "standard" optimizations for recovering
uncurried applictaions.

Maybe another way of looking at this is via s-expr notation::

    e |> (a ... z) ==> (a ... z e)
    e |> (x)       ==> ((x) e)
    e |> x         ==> (x e)

Putting e in the first operand place ``(a e ... z)`` would also work,
but using  ``e |> f x``  for   ``f e x``   competes with  ``e `f` x``.

This is currently a built-in macro, but could be a user-defined macro
with an appropriate macro system.

Precedence (TODO)::

    |> binds tighter than >^
    |> binds looser than everything else?
          x |> f `or` g
                              (x |> f) `or` g   ?
                                x |> (f `or` g)  ?

          f x `or` g resolves as  (f x) `or` g
                    rather than  (f `or` g) x


                                  (f x) `or` g
                                    (f `or` g) x

                                  f :: x => t
                                or :: (x => t) => g => r
      Or no defined precedence, so must explicitly parenthesize?

