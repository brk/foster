Type Inference and Overloading
------------------------------

Here's a snippet of code::

    fn () {
      let s:i64 = llvm.readcyclecounter() in {
        expect_i32(2)
        print_i32(read_i32())
        let e:i64 = llvm.readcyclecounter() in {
          expect_i1(true)
          print_i1(128 < (e - s))
        }
      }
    }

and its corresponding lambda-desugared AST::

    ├─FnAST
    │ └─CallAST
    │   ├─FnAST (binding s)
    │   │ └─SeqAST
    │   │   ├─CallAST
    │   │   │ ├─VarAST       expect_i32
    │   │   │ └─IntAST       2
    │   │   ├─CallAST
    │   │   │ ├─VarAST       print_i32
    │   │   │ └─CallAST
    │   │   │   └─VarAST       read_i32
    │   │   └─CallAST
    │   │     ├─FnAST (binding e)
    │   │     │ └─SeqAST
    │   │     │   ├─CallAST
    │   │     │   │ ├─VarAST       expect_i1
    │   │     │   │ └─BoolAST      True
    │   │     │   └─CallAST
    │   │     │     ├─VarAST       print_i1
    │   │     │     └─BinaryOpAST  <
    │   │     │       ├─IntAST       128
    │   │     │       └─BinaryOpAST  -
    │   │     │         ├─VarAST       e
    │   │     │         └─VarAST       s
    │   │     └─CallAST
    │   │       └─VarAST       llvm.readcyclecounter
    │   └─CallAST
    │     └─VarAST       llvm.readcyclecounter

----

Suppose we are given
  * ``llvm.readcyclecounter :: () -> i64``
  * ``expect_i32 :: i32 -> ()``
  * ``expect_i64 :: i64 -> ()``
When we see this::

    │     │   ├─CallAST
    │     │   │ ├─VarAST       expect_i32
    │     │   │ └─IntAST       2

we should infer that ``2 :: i32``, and the ``CallAST`` node has type ``()``.

But if we saw::

    │     │   ├─CallAST
    │     │   │ ├─VarAST       expect_i64
    │     │   │ └─IntAST       2

we should infer that ``2 :: i64``, and the ``CallAST`` node has type ``()``.

-----

Now, what about typing ``e - s``::

    │     │     │       └─BinaryOpAST  -
    │     │     │         ├─VarAST       e
    │     │     │         └─VarAST       s

This is equivalent to ``(-) e s``::

    │     │     │       └─CallAST
    │     │     │         ├─VarAST       (-)
    │     │     │         ├─VarAST       e
    │     │     │         └─VarAST       s

Well, what's the type of binary ``-``? It "should" be overloaded for (at least)
types ``i32`` and ``i64``.

The Haskell approach here (I think) is to notice
that ``(-)`` is a symbol associated with (only!) the type class ``Num`` with
signature ``(-) :: a -> a -> a  with Num a``. So, when seeing an application
of ``(-) e s``, the type inferencer generates a fresh type variable ``a`` to
represent the type of the application, and generates constraints
``typeof(e) = a``, ``typeof(s) = a``, and ``Num a``.
It is then the obligation of the context of the call to provide evidence that
the types of ``e`` and ``s`` are instances of ``Num``. Evidence, in this case,
would consist of an implementation of ``(-)`` from an instance declaration.

Without type inference, the solution for a general overloaded call is to
look up the *set* of types associated with the overloaded symbol, then
recursively typecheck the arguments to determine their types. Finally,
the set of overloaded types must be resolved against the concrete types
of the arguments, looking for most specific matches. If there is one most
specific match, great; otherwise, issue an error.

There are two differences of assumption between the two approaches:
  * The first question is whether the type checker knows, at the point of
    application, the complete set of overloads available.
    A consequence of the Haskell approach is that type class instances may be
    given post-hoc, which is not possible under the C++ model.
  * The second question is whether the types of the arguments are assumed to
    be known, or whether they are just given by type variables.
