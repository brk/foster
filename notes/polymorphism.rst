The Problems of Polymorphism
----------------------------

Greg Morrisett lays out some issues with compiling polymorphism:
http://www.eecs.harvard.edu/~greg/cs256sp2005/lec15.txt

Here's (top-level) Haskellish pseudo code to illustrate some implementation
issues/decisions to be made regarding implementing polymorphism:

.. code-block :: haskell

    -- A known polymorphic function; easy for the compiler
    -- to specialize at compile-time.
    id :: forall a, (a -> a)
    id x = x

    -- The definition of the identity function, specialized to f64 values.
    -- This is what we want the compiler to produce for id:[f64]
    id_f64 :: f64 -> f64
    id_f64 x = x

    -- A higher-order function involving passed-in function of concrete type
    -- which "wants" args to be passed in special registers on most machines...
    app_f64 :: f64 -> { f64 -> f64 } -> f64
    app_f64 x f = f x

    -- Let-polymorphic generalization of the above function.
    app_gen1 :: forall a, a -> { a -> a } -> a
    app_gen1 x f = f x

    -- The same function, but involving rank-2 polymorphism.
    app_gen2 :: forall b, b -> (forall a, { a -> a }) -> b
    app_gen2 x f = f:[b] x

    -- uid is an unknown function with the identity function's signature.
    issues :: int -> { forall a, a -> a } -> ()
    issues x uid =
    {- a -}   uid:[f64] 42.0
    {- x -}    id:[f64] 42.0
    {- We can statically specialize id for floats, but we can't
       statically specialize uid. Therefore our choices are:

         # (Java) Forbid specialization over non-uniform types,
           and lose much of the convenience of abstracting over types.
           In effect, force programmers to perform boxing & unboxing by hand.
         # (Variant of the Java solution):
           Finesse the issue, remove unboxed floats (etc) as first-class types;
           provide .e.g. boxed floats and arrays-of-unboxed floats, maybe with
           unboxed floats as a separate kind of type. I think this is basically
           what Haskell does. At the moment, this is the most appealing long-
           term option I see.
         # (ML) Forbid higher-rank polymorphism, so that it's not legal to
           pass uid in the first place. Thus every instantiation is done on
           a known function, so monomorphizing code is easy, but we lose
           separate compilation.
         # (O'Caml) Force uniform representations, and make monomorphic code pay
           the price. Not pragmatic, and probably complicates interop with GPUs.
           It's not clear what the actual costs of this option are, though.
         # (FLINT) Flexible representation analysis:
           Hybrid of type passing and coercions. Somewhat complicated.
         # (FRITA) Extend TIL to work on polymorphic and existential types;
           somewhat complicated.
         # (Church) Polymorphism as products/adopt union and intersection types.
           Complicated, not well explored.
         # (just dumb) Give the two specializations different function types,
           effectively tracking the calling convention for function arguments
           via types. This isn't very appealing.
         # (Leroy) Have the "caller" generate coercions around the uniform id
           function which convert from (& back to) non-uniform representations.
           This doesn't work for code involving recursive data types or arrays.
         # (TIL) Do dynamic type dispatch with a ``typecase`` construct.
           Non-trivial runtime overhead for realistic examples.
    -}

    {- b -}   app_f64 42.0 (uid:[f64])
    {- c -}   app_gen1:[f64] 42.0 (uid:[f64]])
    {- d -}   app_gen2:[f64] 42.0  uid

    {- y -}   app_f64 42.0 ( id:[f64])
    {- z -}   app_gen1:[f64] 42.0 ( id:[f64]])
    {- q -}   app_gen2:[f64] 42.0   id
    ) ; ()

Inside the body of ``issues``, ``uid`` is bound to an unknown function.
That implies that when ``uid`` is instantiated to (presumably) different
result types, its implementation---including its calling convention---cannot
be specialized for specific types.
In other words, each argument must be passed in a general-purpose register.
So e.g. on a 32-bit machine, a 64-bit floating point arg must be boxed.

Line by line:

* ``a``: ``uid:[f64]`` requires a uniform argument, so ``42.0`` must be made
  uniform as well, presumably by boxing.
* ``b``: ``42.0`` need not be made uniform when it is passed to ``app_f64``,
  but inside ``app_f64``, ``f`` is an unknown function. Because it is unknown,
  we must conservatively assume it could be an instantiation of a higher-order
  polymorphic function. So now we have at least
  two choices: if we pass our uniform function as-is to ``app_f64``, then we
  are basically forced to box all parameters to all functions. This is, of
  course, unacceptable.
  Or, we could instead create a wrapper with type ``(f64 -> f64)``:
  ``uid_f64_wrapper unboxed_x = unbox(uid_generic(box(unboxed_x)))``.
  But this doesn't work if we have, say, an array of f64 that we want to
  map a polymorphic function over...
* ``c``: We have basically the same question, but now it applies to both
  the (presumed "known") definition ``app_gen`` as well as the unknown ``uid``.
  We could specialize ``app_gen`` to take an unboxed ``x`` arg, and
  (independently) expect the function arg to take (un)boxed args.
* ``d``: This mainly highlights the extra freedom given by ``app_gen1``.

Many of the decisions above depend on whether we're instantiating a known or
unknown function:

* ``x``: because we have the definition of ``id``, we can perform type
  instantiation at compile time, producing a completely specialized ``id_f64``.
* ``y``: see ``b``, only make the reverse decision...
* ``z`` and ``q``: mostly as with ``c`` and ``d``.

Polymorphically Problematic Types
+++++++++++++++++++++++++++++++++

 * Integers of non-pointer size
 * Unboxed structs (pairs, array sections?)
 * Floating point numbers
 * SIMD Vectors

Observation: most of these types are of the most interest in unboxed arrays!
Perhaps they can be given a separate kind from ``Type``, and instantiation over
higher-rank polymorphic values restricted to only types of uniform kind?
(Instantiation over known functions can still be done at compile time
for all types, I think?)

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



Polymorphic Recursion
+++++++++++++++++++++

Consider the following code adapted from `the Church project
<http://www.church-project.org/reports/electronic/Hal+Kfo:BUCS-TR-2004-004.pdf>`_::

    type case T a
           of Empty
           of Node a (T (T a))

    collect = { t =>
      case t
        of Empty    -> []
        of Node n t -> n :: concatMap collect (collect t)
    }

The type of concatMap is ``(a -> [b]) -> [a] -> [b]`` and collect is
``T a -> [a]``.
In the Node case, ``t :: T (T a)``, so ``(collect t) :: [T a]``,
and thus ``concatMap collect (collect t) :: [T a]``. That is, with explicit
type annotations, we'd have ``concatMap collect:[a] (collect:[T a] t)``.
Note that we've had to instantiate ``collect`` at two different types;
thus we have an instance of polymorphic recursion.


The Okasaki example from page 143::

        data Seq = Nil | Cons a (Seq (a, a))

        sizeS seq = case seq of
                        Nil -> 0
                        Cons x xs -> 1 + 2 * sizeS xs

"The outer ``sizeS`` has type ``(Seq a) -> Int`` but the inner has type
``(Seq (a, a)) -> Int``."


Impredicative Polymorphism
--------------------------

The value restriction in ML arises (in part?) because predicative polymorphism
cannot assign the correct type to a reference to the identity function.
The correct type is ``(ref (forall a (-> a a)))`` but with stratified
polymorphism, the closest approximation is ``(forall a (ref (-> a a)))``
which allows the writer and reader of such a mutable reference to disagree.

To summarize, impredicative polymorphism is neeeded for encoding existentials,
as well as polymorphic recursion and functions like Haskell's ``runST``.
Predicative (let-) polymorphism favors runtime performance at the expense
of compilation time and program expressiveness.

I'm not entirely convinced that it's better to encode existentials with
impredicative polymorphism versus directly including strong sums in the
language. But I think the other arguments are sufficient to make full System F
strongly worth considering.

Our Solution
++++++++++++

Our proposed solution is a systems-oriented variant of what Haskell does.
We use a system of kinds to distinguish types---and, crucially, type
variables---which are represented uniformly from those which are not.
The key is that type variables quantified by forall types have associated
kinds.  We use this information in two ways:

  #. We do not permit functions with unboxed polymorphic arguments
     to be passed in a higher-order way; higher kinds are restricted
     to abstraction over boxed types.
  #. We do not permit instantiating a boxed type variable with an
     unboxed type.

As a result, the type system enables use of uniform representations
where needed, and unboxed representations where possible.

It's worth noting that the example of ``map id list-of-unboxed-floats``
is forbidden by the type system, whereas with a Leroy-style coercion
system, the compiler would be forced to traverse the list at runtime
to be able to pass a list of boxed floats to ``map`` for ``id`` to use.
Making this cost explicit is why I call this this scheme systems-oriented.

Haskell has unboxed kinds (or rather GHC does via a nonstandard flag),
but partly because they leave instantiation and generalization implicit,
ML-style, they leave kinds more implicit and second-class than we do.
One tactic I think they got right, compared to Java, is to make the "default"
base types like ``Char`` and ``Float`` boxed rather than unboxed.
This meshes well with making integers arbitrary-precision by default,
with fixnums as unboxed types.

Generalization, Meta Type Variables, and Big Lambdas
++++++++++++++++++++++++++++++++++++++++++++++++++++

The following code type-checks in Haskell::

    foo x = bar x
    bar (_ :: [b]) = ()

Haskell will implictly generalize the type of ``foo`` to ``forall a. [a] -> ()``.

However, if we add a type annotation to ``foo``, like so::

    foo :: z -> ()
    foo x = bar x
    bar (_ :: [b]) = ()

the code no longer typechecks. The reason is that ``z`` denotes an opaque type,
rather than a type meta variable. Unification would produce ``z = [b]`` which
is an error.

In Foster, at least for now, the situation is reversed. In the first example,
instead of implicitly generalizing ``foo`` to have a polymorphic type,
we give ``foo`` a non-polymorphic type involving a unification variable.
(One downside is that using an un-annotated ``foo`` polymorphically will result
in a sub-optimial error message, although that is a fixable problem).
To get polymorphic behavior, ``foo`` must be given an explicit polymorphic binder,
which can be done using a type annotation::

    foo :: forall t:Type, { t => () };
    foo = { x => () };

or on the value-level lambda directly::

    foo = { forall t:Type, x : t => () };

Note that ``{ forall t:Type, x => () }`` results in ``x`` getting a type metavariable,
rather than the presumably-intended behavior of getting the bound type variable ``t``.

But Why?
++++++++

The major advantage of this approach is that every language-level type variable has
an explicit binding site, which in turn means that scoped type variables are trivially
supported, rather than the situation in Haskell, where they are a non-standard extension.
Being explicit about type variable binding sites also improves the robustness of
inference for effects and rows when appearing in higher order function type annotations.

Links
+++++

  * Compiling with Polymorphic and Polyvariant Flow Types
     <http://www.church-project.org/reports/electronic/Tur+Dim+Mul+Wel:CPPFT-1997.pdf>
  * Programming Examples Needing Polymorphic Recursion
    <http://www.church-project.org/reports/electronic/Hal+Kfo:BUCS-TR-2004-004.pdf>
  * `Polymorphism by Polyinstantiation <http://www.bitc-lang.org/docs/bitc/polyinst.html>`_
    (and associated bibliography)
  * JGM's lecture notes on polymorphism
     <http://www.eecs.harvard.edu/~greg/cs256sp2005/lec15.txt>
  * Working around limitations of whole-program monomorphism
     <http://lambda-the-ultimate.org/node/4091>
  * Code expansion due to monomorphization in MLton?
     <http://mlton.org/pipermail/mlton/2001-January/018367.html>
  * PRACTICAL TYPE INFERENCE FOR FIRST-CLASS POLYMORPHISM
    <http://research.microsoft.com/en-us/people/dimitris/dimitriv-dissertation-post.pdf>
  * "The effectiveness of type-based unboxing"
  * "A calculus for boxing analysis"

