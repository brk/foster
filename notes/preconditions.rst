Preconditions (etc)
===================

An array subscript expression ``a[i]`` can be compiled without a dynamic index
check iff we can prove that ``i <=u arrayLength a`` (relying on the invariant
that ``arrayLength a >=s 0``).

In order to discharge such an invariant, we often must have invariants on
function arguments (that is, preconditions).

We can represent a function precondition as a synactic function from arguments to
a predicate expression. That is, the function ``{ v : Int32 => ... }`` could be given the
precondition ``{ pv : Int32 => pv !=Int32 0 }`` to ensure that it is only called
with non-zero values. Note that this is morally equivalent to the more traditional (?)
dependent refinement type syntax ``{ v : (pv:Int32|pv !=Int32 0) => ... }``
except that refinements are not permitted on any types except those used as function arguments.

In order that invariants on function arguments are always statically satisfied,
we must either severely restrict the uses/propagation of functions with static
checks, or reflect the static checks in the type system, giving all function
types a static precondition.

If we pass argument ``x`` when calling a function ``f`` with a precondition ``pf``,
then we must statically verify that ``pf x`` holds.

If we pass argument ``f`` when calling a function ``g``, where ``g``'s formal
argument ``h`` has a precondition ``ph``, then we must statically verify that
``ph ==> pf``. We currently implement this check by generating fresh skolem
constants to represent the arguments, and then check that ``ph skols ==> pf skols``.

Preconditions establish facts about arguments to functions, but cannot establish
facts about the results of function applications. Postconditions are often
necessary, for example to verify that loop invariants are maintained.


We can easily infer facts about primitive operations, but by default
(to maintain scalability of checking) we don't infer any results about
lambda abstractions. This means that all lambdas are opaque, and all summarization
of return value properties must be provided manually, by postconditions.

Handling of postconditions is dual to preconditions: calls establish the postcondition,
and higher order usage is covariant.

Compared to refinement types, this approach seems awkward for propagating information
through intermediate data structures. For example, the utf8-decoder example
represents loop state as a pair, which means we need an invariant (postcondition)
on the pair. Thus we'll have a postcondition ``{ pr => case pr of (s,_) -> ... }``
on the loop body, along with an expression deconstructing the result of the loop body
``case loopbody ... of (st, _) -> loop ... end``. With refinemnt types, the intermediate pair
has the type ``((s:Int32|...), Int32)``, which serves to connect the postcondition with the use,
propagating the refinement in the expression to the bound variable ``st``.
In contrast, if we have only explicit pre/post-conditions and cannot rely
on the compositionality of types, we must conjure up some way of lifting predicates
on integers to pairs, and again of un-lifting back to the individual binder.
Types seem like a much more natural vehicle for carrying this information.

Propagating refinements via a unification-based algorithm is rather trickier
than it might first appear. On the one hand, refined types should be allowed to
unify with their un-refined counterparts, in most circumstances.
However, whether the refinement should
be propagated or not is somewhat subtle! If the refinement is never propagated
then, for example, refinements in type annotations will not be available within
the body of the separately-annotated expression. On the other hand, if every
unification propagates refinements, then a function like
``{ v1 : %r1 : Int32 : p => v2 : Int32 => v1 +Int32 v2 }``
will wind up propagating ``v1``'s refinement to ``v2``, which is not correct!

Another case has to do with numeric literals, which are always given a
meta-variable for a type, to ensure that literals are given the most appropriate
type according to their usage in the program. However, this means that if a
function ``f`` has a refined argument, then the application ``f 0`` will
propagate the argument's refinement to the literal ``0``, which is blatantly
wrong! For example, if the refinement is something like ``%r : Int32 : r != 0``
then the K-normalized code ``let x = 0 :: (%r : Int32 : r != 0) in f x`` will
have the contradiction ``0 != 0`` in scope when checking the call ``f x``,
and the overall result is that the refinement on ``f`` is not checked!

Scoping of refinement variables is also somewhat murky.
The "top-level" refinements of a function's parameters should be recursively
scoped with each other. However, it's not immediately clear why unification
cannot push a bound variable outside the scope of its binder.
That is, given a function with a type like
``{ % rx : Int32 : ... => % rv : Int32 : rv > rx }``
the result of applying the function would seem to be the type
``% rv : Int32 : rv > rx`` which is ... not well formed?
But maybe it's OK because during SMT-based checking we will instantiate
the type for the application ``f xv`` so the type becomes ``% rv : Int32 : rv > xv``...

Another example::

    foo :: { % aa : Int32 : True
          => % bb : Int32 : bb >UInt32 aa
          => () };
    foo = { a => b => 42 };
    foo 0 1;

First, the formals ``a`` and ``b`` will be given meta type variables,
which will be unified with the corresponding refined type annotations.
Then, the constant ``1`` will be assigned a meta type variable.
which will then get unified with the type of the parameter. Thus the constant
``1`` will be given the ill-formed type ``% bb : Int32 : bb >UInt32 aa``.

Or, actually, that's one way it could happen. The way it actually happens is
perhaps even worse. With direct type annotations on foo, the constants will be
typechecked against (Check (RefinedType ...)), and will thus directly scoop up
the refined versions of the function parameter types.

Combining these two is a real bear, since it's not clear that we can (say) strip
off the refinement if the parameter happens to be a meta type variable due to a
separate annotation...


As indicated above, unification is not the right way to propagate refinements,
because unification is bidirectional but the refinement relation is
unidirectional. This immediately suggests subtyping, or rather, subsumption.
However, subsumption is also not the right relation to use. Consider:
a type annotation ``{ (%ra : ...) => (%rv : ....) }`` on a function literal
``{ a : A => b }``. Intuitively, both annotations (``%ra`` and ``%rv``) should
flow in the same direction, towards the type annotations on ``a`` and ``b``,
respectively. However, the nature of subsumption will have
``%ra`` and ``%rv`` on "opposite" sides of the relation!

Thus, we propagate refinements "manually" when encountering top-level type
annotations.


Another technical challenge:
When typechecking a function which does not have a complete Haskell-style
separate annotation, we must generate a skeleton fn-type to use for checking
recursive calls (especially of polymorphic functions). The resulting type should
be a "checked" type (that is, TypeTC, not TypeAST). However, that in turn means
that we will need to convert the type annotations on the function's arguments
from TypeAST to TypeTC, which involves checking any refinements. Since refinements
can be recursive, we must process a complete FnType to set up the proper env,
and must not process each annotation individually, for that will break rec-refs.
The challenge: what do we use to represent missing annotations? TypeAST does not
have direct unification variables. MetaPlaceholderAST becomes a tau unification
variable, but we really want a sigma!

Functions involved in type inference/propagation::
    tcRhoBool/tcRhoText/tcRhoArrayLit/.../subsCheckRho[Ty]
      unify
        tcUnifyTypes
          tcUnifyLoop
            tcUnifyRefinements :: RR -> RR        -> Tc ()
            refineRefinement   :: RR -> (Id,Expr) -> Tc ()

