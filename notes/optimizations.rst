Optimizations
-------------

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

Waddell and Dybvig [4] present a linear-time (but incomplete) algorithm for general, unrestricted
beta reduction interleaved with constant propagation with several desriable properties
(online, polyvariant, context-sensitive, demand-driven). A variant of this algorithm is implemented
in ``KNExpr.hs``.


#. `Compiling with Continuations, Continued <http://research.microsoft.com/en-us/um/people/akenn/sml/CompilingWithContinuationsContinued.pdf>`_
#. `Shrinking Lambda Expressions in Linear Time <http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.55.7347&rep=rep1&type=pdf>`_
#. `Compiling Standard ML to Java Bytecodes <http://research-srv.microsoft.com/en-us/um/people/nick/icfp98.pdf>`_
#. `Fast and Effective Procedure Inlining <http://www.cs.indiana.edu/~dyb/pubs/inlining.pdf>`_


GC Optimizations
~~~~~~~~~~~~~~~~

Liveness allows optimizing use of gc roots::

        // IN: 2 3 5 8 13 21

        // * If a function body cannot trigger GC, then the in-params
        //   need not be stored in gcroot slots. Reason: the params
        //   are never live after a GC point, because there are no GC points.
        //
        fn-no-gc = fn (n : i32, r : ref i32) {
          expect_i32(deref(r))
          print_i32(n)
        }

        may-trigger-gc = fn (to i32) { let x : ref i32 = new 0 in { deref(x) } }

        // * If there are no GC points after a `new`, then the returned
        //   pointer need not be stored in a gcroot slot. Reason: there
        //   are no further GC roots across which the pointer must be stored.
        //
        // TODO enable once regular local vars are implemented
        //no-gc-after-new = fn (to i32) {
        //  may-trigger-gc()
        //
        //  let n : ref i32 = new 0 in {
        //    0
        //  }
        //}

        // * If a pointer is dead after being passed to a function,
        //   then it need not exist in a gcroot slot after the previous
        //   GC point. Thus the temporary in `f(new blah)` need not be
        //   stored in a gcroot slot. Reason: not live for GC.
        //
        no-root-for-dead-ptrs = fn () {
          expect_i32(42)
          print_i32(deref(new 42))
        }
        main = fn () {
          fn-no-gc(30, new 30)
          //no-gc-after-new()
          no-root-for-dead-ptrs()
        }

Data Structure Elimination
~~~~~~~~~~~~~~~~~~~~~~~~~~

The following idioms should not involve runtime allocation::

        case (x1, ..., xn) of ... end

        let v = (x1, ..., xn) in case v of ... end end

We can also generalize this in a few ways.
First, this works for any single-constructor datatype, not just tuples.
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

Pipe Operator
~~~~~~~~~~~~~

The pipe operator::

    b |> bytesDrop todrop

is syntax for::

    (     bytesDrop todrop  b   )
    (NOT (bytesDrop todrop) b  !)

and::

    (b |> bytesDrop todrop |> bytesTake reslen)
    =~=
    (b |> bytesDrop todrop) |> bytesTake reslen

is syntax for::

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

