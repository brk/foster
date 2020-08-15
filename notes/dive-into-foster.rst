Dive Into Foster
================

Foster is an evolving language.
This document introduces what exists, then discusses potential future features.

Current Status
--------------

We begin, as is tradition, by saying hello.

Hello World
~~~~~~~~~~~

Here's the Foster version of 'Hello, World'::

    snafuinclude Prelude "prelude";

    main = {
      print_text "Hello, World";
    };

Two shortcomings are already apparent.
First, the syntax for importing code is a temporary placeholder, mirroring the fact
that the implementation (essentially a slightly smarter ``#include``) is a temporary hack.
A proper module system is planned future work.
Second, Foster also currently lacks any form of overloading or ad-hoc polymorphism;
there is no generic ``print`` function.

Running Code
~~~~~~~~~~~~

To run an individual file, use ``runfoster``:

.. code-block:: bash

    :2016-09-07 16:06:09 ~/foster/_obj/ $ cat scratchpad.foster
    snafuinclude Prelude "prelude";
    main = {
      print_text "Hello, world!";
    };
    :2016-09-07 16:06:11 ~/foster/_obj/ $ runfoster scratchpad.foster
    Hello, world!

Alternatively, use ``fosterc`` to compile to an executable.

The ``test/bootstrap`` directory contains the primary regression suite for
the compiler. The ``gotest.sh`` script finds and run tests by name, and
prints out a bunch of debugging/timing info along the way::

    :2016-09-07 15:41:30 ~/foster/_obj/ $ gotest.sh coalesce-loads
    testing /home/benkarel/foster/test/bootstrap/testcases/coalesce-loads
    [0/1] cd /home/benkarel/foster/_obj && python /home/benkarel/foster/scripts/mk_me.py --srcroot /home/benkarel/foster --bindir /home/benkarel/foster/_obj --optimize
    python /home/benkarel/foster/scripts/run_test.py --show-cmdlines /home/benkarel/foster/test/bootstrap/testcases/coalesce-loads/coalesce-loads.foster
    ::^^^:: /home/benkarel/foster/_obj/fosterparse /home/benkarel/foster/test/bootstrap/testcases/coalesce-loads/coalesce-loads.foster /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads.foster.parsed.cbor -I /home/benkarel/foster/stdlib

    Performing shrinking: False
    /// Mono    size: (20,194)
                                                (initial query time, overall query time)
    # SMT queries: 0 taking []
    typecheck   time: 5.856 ms     (20.6%)
    inlining    time: 2.861 μs      (0.0%)
    shrinking   time: 5.960 μs      (0.0%)
    monomorphiz time: 228.9 μs      (0.8%)
    static-chk  time: 518.1 μs      (1.8%)
    cfg-ization time: 1.498 ms      (5.3%)
    codegenprep time: 7.706 ms     (27.1%)
    'other'     time: 12.60 ms     (44.4%)
    sum elapsed time: 28.41 ms    (100.0%)

    CBOR-in     time: 83.92 μs      (0.3%)
      capnp-out time: 24.50 ms     (86.2%)
    overall wall-clock time: 53.00 ms
    # source lines: 71
    source lines/second: 1339.7
    ::^^^:: /home/benkarel/foster/_obj/me /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads.foster.parsed.cbor /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads.foster.checked.pb +RTS -smeGCstats.txt -K400M -RTS --interactive
    ============== fosterlower =============
            Category name                  Total     Local
            io                             57 ms      0 ms
            io.capnp                        2 ms      0 ms
            io.capnp.read+translate         2 ms      2 ms
            io.file                        55 ms      0 ms -- Time spent doing non-parsing I/O (ms)
            io.file.dumpmodule             23 ms      0 ms
            io.file.dumpmodule.bitcode     20 ms     20 ms
            io.file.dumpmodule.ir           2 ms      2 ms
            io.file.readmodule             32 ms     32 ms
            llvm                           11 ms      0 ms
            llvm.link                      11 ms     11 ms -- Time spent linking LLVM modules (ms)
            total                          75 ms     75 ms -- Overall compiler runtime (ms)
    ::^^^:: /home/benkarel/foster/_obj/fosterlower /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads.foster.checked.pb -o coalesce-loads.foster -outdir /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads -fosterc-time -bitcodelibs /home/benkarel/foster/_obj/_bitcodelibs_ -dump-prelinked
    ============== fosteroptc =============
            Category name             Total     Local
            io                        93 ms      0 ms
            io.file                   93 ms      0 ms -- Time spent doing non-parsing I/O (ms)
            io.file.dumpmodule        63 ms      0 ms
            io.file.dumpmodule.ir     63 ms     63 ms
            io.file.readmodule        29 ms     29 ms
            llvm                     536 ms      0 ms
            llvm.llc+                525 ms    525 ms -- Time spent doing llc's job (IR->obj) (ms)
            llvm.opt                  11 ms      9 ms -- Time spent in LLVM IR optimization (ms)
            llvm.opt.memalloc          2 ms      2 ms
            total                    631 ms    631 ms -- Overall compiler runtime (ms)
    ::^^^:: /home/benkarel/foster/_obj/fosteroptc /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads.foster.preopt.bc -fosterc-time -o /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads.foster.o -tailcallopt -O0 -dump-preopt -dump-postopt
    ::^^^:: /home/benkarel/llvm/3.7.0/bin/clang++ /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads.foster.o /home/benkarel/foster/_obj/_nativelibs_/libfoster_main.o /home/benkarel/foster/_obj/_nativelibs_/libchromium_base.so /home/benkarel/foster/_obj/_nativelibs_/libcoro.a /home/benkarel/foster/_obj/_nativelibs_/libcycle.a -lpthread -lrt -lglib-2.0 -latomic -o /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads -Wl,-R,/home/benkarel/foster/_obj/_nativelibs_
    ::^^^:: /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/coalesce-loads < /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/_extracted_input.txt > /home/benkarel/foster/_obj/test-tmpdir/coalesce-loads/actual.txt


            \m/_(>_<)_\m/    (13 lines)


    fpr:  48 | fme:  58 | flo:  88 | foc: 643 | as+ld:  37 | run:  25 | tot:  899 | coalesce-loads
    fpr:  5% | fme:  7% | flo: 10% | foc: 74% | as+ld:  4%
    input CBOR 24.4 KB (507.3 KB/s); output protobuf 22.9 KB (394.7 KB/s); object file 278.6 KB (381.1 KB/s)
    ------------------------------------------------------------
    :2016-09-07 16:03:20 ~/foster/_obj/ $


Syntax
~~~~~~

Files are a collection of top-level *items*: definitions of constant values like
functions, integers, and arrays, plus declarations of external symbols.
Unlike in C, function definitions do not have to be given in dependency order;
that's the compiler's job to figure out.
Functions look like this::

    incrementByOne = { a => a +Int32 1 };

A function has zero or more parameters, each one followed by a thick arrow (``=>``).
Type inference determines that the parameter ``a``, and the function's result,
both have type ``Int32``.
It's often easier to read code when functions are given explicit type annotations::

    foo :: { Int32 => Int32 => Int32 };
    foo = { a => b => a +Int32 b };

You can also put type annotations inline, on individual parameters::

    foo = { a : Int32 => b => a +Int32 b };

Like in Haskell, you can use ordinary names as infix operators with backticks,
and turn operators into names with parens::

    // (foo 20 3) will print 123
    foo = { x => y =>
      bar = { a => b => (((+Int32) a b) +Int32 100 };
      //                  ^^^^^^^^ prefix notation for infix operator
      x `bar` y
      //^^^^^ infix notation for a regular function call
    };

Line comments use ``//`` like in C++.
Less obviously, ``/* ... */`` is a *nesting* block comment.

Identifiers
~~~~~~~~~~~

Names must start with a letter or underscore,
and may be followed by letters, digits, underscores,
or any the following: ``+*!><?-=``.
(Notably absent: ``^``, because it's a postfix operator; ``foo^`` must parse as ``foo ^``).

Operators start with one of the above symbol characters,
and may contain embedded ``^`` characters as well as any legal name character.

Operator Syntax
~~~~~~~~~~~~~~~

Unlike C, there's no overloading or implicit conversion, so ``+Int32``
is a separate function from ``+Int64``. Also, signedness is a property of
operations rather than values: there are separate
``>UInt32`` and ``>SInt32`` primitives, but no separate add/mul/etc functions,
which produce identical bitpatterns for "signed" and "unsigned" values.

There are explicit checked add/sub/mul operators,
which do come in signed and unsigned variants:
``+ucInt32``, ``*scInt64``, etc.
These operators dynamically check for wraparound (in LLVM, using intrinsics
which can do things like check hardware overflow flags).
On overflow, the checked operator variants currently abort the program.
These primitives will likely be overhauled in the future; for now they can
help estimate the potential cost of pervasive (location-precise) overflow checking.

Bitwise operators are spelled like ``bitand-Int32``. The primitive bitwise operators are
``bitand``, ``bitor``, ``bitxor``, ``bitshl``, ``bitlshr``, ``bitashr``, and ``bitnot``.
There's also ``ctlz`` and ``ctpop``.
There are higher-level functions defined in ``stdlib/bitwise/bitwise.foster``.

Expressions
~~~~~~~~~~~

A function body, as demonstrated above, is a series of parameters,
followed by a series of bindings or expressions, such as function calls,
which are written in Haskell/ML style: ``f arg1 arg2``. Unlike those languages,
functions aren't curried. That is, there's a distinction between a function
that takes two arguments, and one that takes one argument and returns a function
that takes another argument. To call a function that returns a function, use
``(f arg1) arg2``.

A function literal of zero arguments can be called with a postfix ``!``.
Thus ``{ e } !`` is semantically equivalent to ``e``. This idiom is
sometimes useful to give tightly scoped names to parts of expressions,
as in ``{ foo = bar baz; do-something-with foo }``.

Precedence
++++++++++

``bits `bitand-Int64` mask ==Int64 0``
=
``bits `bitand-Int64` (mask ==Int64 0)``

whereas

``bitand-Int64 bits mask ==Int64 0``
=
``(bitand-Int64 bits mask) ==Int64 0``

The Pipe Operator
+++++++++++++++++

Functions can also be applied F#-style, using the pipe operator:
``arg2 |> fn arg1 |> { x => foo x y }``.
This pipeline is desugared by the compiler into ``{ x => foo x y } (fn arg1 arg2)``
which is guaranteed to be shrunk to ``foo (fn arg1 arg2) y``.

In languages with currying, all arguments are of a single function;
syntax like ``fn arg1 arg2`` means the same thing as ``(fn arg1) arg2``
and so the pipeline operator can be defined as a regular function.
With uncurried arguments, the pipeline operator must be primitive in
order to work with functions of any number of arguments.
Having multiple arguments also raises the question of which argument
"receives" the pipe's input.
In some languages, the answer is the function's first argument.
Foster's pipeline operator applies its argument to the *last* 
argument, not the first.
As the previous example shows, this potential ambiguity can be resolved with
minimal syntactic overhead with a function literal.

.. todo
  I'm considering whether having two pipe variants for "near"/"far"
  applications might be a worthwhile tradeoff. Potentially with
  ``|>>`` for far and ``|>`` for near, or keep ``|>`` for far and
  use something like ``..`` for near, mirroring/reflecting the
  connection between record field lookup and functional methods.

Other expressions include pattern matches
``case e of p1 -> e1 of p2 -> e2 end``, conditionals ``if a then b else c end``,
tuples ``(a, b, c)``, records ``(x : a, y : b, z : c)``, and literals.

Literals
++++++++

Foster has integer literals of unconstrained size,
plus floating point rational numbers.

Strings use Python-like syntax: single or double quotes,
in single or triple-pair flavors; :doc:`strings` can be prefixed with ``r`` to
disable escaping, or ``b`` to produce bytestrings ``(Array Int8)`` instead
of ``Text``; there is no primitive character type).

There are also boolean literals ``True``/``False`` (of type ``Bool``).

Numeric Literals
++++++++++++++++

Foster currently enforces a strict lexical distinction between integer and
floating point values. 
Integers are allowed to be written in exponential notation (``1e10``)
but if it doesn't have a dot in it, it will not be treated as a floating
point number.
(This is likely to be relaxed in the future.)

Once upon a time, numbers had Fortress-style radix suffixes (like ``8FFF_16``)
but now we use regular hex/binary prefix syntax (``0b1101``). Numbers can have
embedded backticks to provide visual separation: ``0b`1110`1110``.
Binary and hexadecimal (but not octal) literals are supported.
Foster permits the usual decimal and scientific notations for floating point
numbers, as well as the more-recent hexadecimal floating point literals (``0x1.2p3``).

One cute thing the compiler will do is notify you about misleading and/or
potentially interesting alternative ways to write floating point literals.
Like so::

    Warning: the provided rational constant

      9999999999999999.0
      ~~~~~~~~~~~~~~~~~~

    is actually the floating point number 10000000000000000.0
             or, in exponential notation: 1e16


    Warning: the provided rational constant

      x = 1.0000e+00;
          ~~~~~~~~~~

    could be written more compactly as    1e0
                       or, alternatively: 1.0


Integer literals are given an inferred type according to their usage; it is
a compile-time error for the value to be out of range for the type.
For example, the literal ``4294967295`` can be given the type ``Int32`` but
the literal ``4294967296`` cannot be::

    Unable to type check input module:
    Int constraint violated; context-imposed exact size (in bits) was 32
                                  but the literal intrinsically needs 33
      print_i32 4294967296;
                ~~~~~~~~~~

Note that integer literals describe twos-complement bit patterns.
Thus ``255 ==Int8 -1`` is true, whereas ``255 ==Int32 -1`` is false.
The bit pattern denoted by the literal ``-1`` depends on its assigned type.

Pattern Matching
++++++++++++++++

Pattern matches can have guards, and non-binding or-patterns are supported::

    // Evaluates to 200
    case (1, 2)
      of (a, 2) if a ==Int32 2 -> 100
      of  (2, 3)
       or (1, 2) -> 200
      of _ -> 300
    end

Pattern matching doesn't currently support arrays or string constants.

Other Expressions
+++++++++++++++++

Foster provides partial syntactic support for mutable references and arrays.
Arrays allow indexing with postfix ``.[idx]`` syntax.
References can be dereferenced with postfix ``^`` and assigned to with the
(infix) ``>^`` operator.
Unlike ML's traditional right-to-left assignment operator ``:=``,
the reference assignment operator is left-to-right, emphasizing the
distinction between pure binding and mutable update,
and also mirroring the syntax for pipelined application.
As in C, array updates may be done by combining the mutable update
operator with the array indexing syntax.

Some expressions are represented with primitive functions rather than
dedicated syntax. For example, instead of Python-style ``[1, 2, 3]``
for arrays, we get by with ``prim mach-array-literal 1 2 3``.
It's ugly but it retains flexibility.
Better syntax will likely come in the future, but a big question is:
for what data structures?

Primitives
++++++++++

To reduce the syntactic surface area of the language, Foster has a system of **primitives**.
Primitives can only be called directly; they cannot be passed around as callable values the
way that normal functions can. A primitive call is prefixed by the token ``prim``.
Primitives provide a means of extending the language without needing to modify the language's grammar.

Many operators in other languages with built-in syntax (in other languages and in Foster)
can be recast as primitives. Beyond the basic arithmetic operators, examples include
the subscript syntax (``a.[b]`` is equivalent to ``prim subscript a b``)
and deref syntax (``a^`` is equivalent to ``prim deref a``).

Other syntactic elements of Foster can be conceptually translated to primitive calls.
For example, the tuple syntax ``(a, b, c)`` is equivalent to ``prim tuple a b c``,
and it would be possible to recast ``if-then-else`` as a primitive as well.
But not everything; neither function definitions nor pattern matching can be recast as primitive calls.

Some elements that would be syntax in other languages remain primitive-only in Foster, for now,
such as ``mach-array-literal``.

Finally, Foster has some primitives without close analogues in other languages.
``assert-invariants`` hooks into the compiler's static analysis machinery,
and halts compilation if the given expression cannot be statically shown to be true.
``log-type`` directs the compiler to print out the inferred type of the given expression.

In addition to ``subscript``, which will (usually) require dynamic bounds checks to ensure safety,
there are variants that give the programmer more control. ``subscript-static`` requires a static
proof of safety, and in return guarantees that no dynamic bounds check will be emitted.
``subscript-unsafe``, as its name implies, omits the bounds check without proof.

The call ``prim __COMPILES__ e`` takes an expression and evaluates (at compile time)
to a boolean value reflecting whether the provided expression was well-typed.
This can be useful to make sure that "improper" usage of an API
is being prevented by the type system.

.. note::

  Pedantic note: ``__COMPILES__`` does not undo the effects of type checking
  its argument; thus, by modifying unification variables, adding a
  ``__COMPILES__`` primitive to working code can cause other code to fail
  to type check properly.


Statements
~~~~~~~~~~

A function body is a sequence of statements, which are bindings or expressions.
The last statement in the sequence must be an expression.
Statements also appear within control-flow expressions like ``if`` and ``case``.
Semicolons separate statements.
A terminating semicolon on the last expression is allowed; unlike in Rust, its presence
has no semantic meaning.

Bindings of recursive functions
use a ``REC`` marker. Recursion is the only primitive looping construct;
there is no primitive equivalent to ``for`` or ``while`` loops.
Part of the reason is that we can then also exclude ``break`` and ``continue``
statements, which in turn means that functional abstraction becomes more powerful:
unlike in a language with that sort of semi-structured control flow, we can
add function wrappers to arbitrary expressions without disrupting any such control flow.

Destructuring binds are supported for tuples::

   ex = { p : (Int32, Int32) =>
     let (a, b) = p;
     a +Int32 b
   };

At file scope, we can also define new datatypes::

    type case List (a:Type)
           of $Cons a (List a)
           of $Nil
           ;

The ``$`` marker is required to syntactically identify data constructors
(as opposed to bindable variables) in patterns and data type definitions.


Effects and Handlers
~~~~~~~~~~~~~~~~~~~~

Foster includes a system of algebraic effects and handlers.
The design is inspired by much prior work, especially (but not limited to) Koka.

For those with a systems background: effects and handlers are the
linguistic analogue to system calls. They enable a lot of cool stuff!

Typechecking tracks each function's *effects*, which describe the sorts of
actions that might be triggered while executing the function.
As with types, effects can be inferred or written out explicitly.
Syntactically, effects are "attached" to a function's return type.
For example, if ``foo`` is a procedure which takes and returns unit values,
and might have effects ``Eff1`` and ``Eff2``, we'd write its signature like so::

    foo :: { () => () @ (Eff1, Eff2) };

To use higher order functions, we must be able to describe effects abstractly.
For example, when we call the ``listMap`` function, the effect of the call
is precisely the effect of the function we provide. Written out in full,
the ``listMap`` function has a signature like so::

    listMap :: forall (a:Type) (b:Type) (e:Effect)
                  { List a => { a => b @ e } => List b @ e };

We also sometimes want to combine effects. For example, suppose we wanted to
map a list, but also print a message to the console for each element::

    listMapAndLog :: forall (a:Type) (b:Type) (e:Effect)
                  { List a => { a => b @ e } => List b @ (Log|e) };
    listMapAndLog = { list => fn =>
      listMap list { a => log "."; fn a }
    };

The ``(Log|e)`` syntax is called an *open effect*; it just means that calling
``listMapAndLog`` function can perform whatever effect(s) ``fn`` can do,
plus also logging.

A *closed effect* describes a known and finite set of effects.

One subtlety here is that it's often convenient to write a finite list of known
effects in types, but generally what we really mean by that is "at least these
effects", not "exactly these effects". That is, what we usually want is "closed"
syntax but open semantics. Accordingly, the way to actually write a closed effect
is with a trailing closed bar and no variable, like ``(Foo, Bar|)``.
Writing ``(Foo, Bar)`` by itself will be implictly translated to an open effect
``(Foo, Bar|e)`` and the effect variable ``e`` will be implicitly quantified over.


At the value level, we can also declare our own domain-specific effects.
An example to demonstrate the syntax for doing so::

    effect MyEffectType (a:Boxed)
      of $MyEffect      a           => Int32;
      of $MyOtherEffect Int32 Int64 => a;

This allows ``(MyEffectType Foo)`` to be used as an effect, for any boxed type Foo.
It also declares functions to *perform* particular effects.
In this example, the compiler would generate symbols with the following types::

    do_MyEffect      :: forall (a:Boxed) { a              => Int32 @(MyEffectType a) };
    do_MyOtherEffect :: forall (a:Boxed) { Int32 => Int64 => a     @(MyEffectType a) };

Handlers allow us to give specific behavior to a user-defined effect.
An example of the syntax is::

    handle some-effectful-expression !
      of $MyEffect x -> resume 0
      of $MyOtherEffect x y -> resume (generate-an-a !)

      as { fin => ... }
    end

Within the right-hand-side of each "arm" of the handler,
the compiler defines a function called ``resume`` which takes
a value of the effect constructor's return type. Calling the ``resume``
function transfers control back to call that was performing the effect.
A handler doesn't have to call ``resume``; for example, if we wanted to give
our effect exception-like semantics, we would not resume the code that threw
the exception. The ``resume`` function is a *tiny* bit magical: it can be stored
in the heap, but it can be called at most once. (The current implementation simply
halts the program; in the future we might have it raise a different effect in turn.)

One other subtlety: The ``resume`` function re-executes the target code with the
same effect handler in place. This is a convenient default, but for more advanced
uses of effect, such as for doing user-level scheduling, we sometimes want to
execute the target code in the presence of a different handler. To do this,
the compiler also silently defines a symbol called ``resume_bare``.

The ``as`` clause is optional; it allows a transformation to be applied to the
return value of the handled code. The difference between ``handle e |> xform of ... end``
and ``handle e ... as xform end`` is that the former runs the ``xform`` function
"under" the handler, and the latter runs it "outside" of the handler. Either way,
the ``xform`` function only applies to the value returned by the handled expression,
not the return value of the handler arms (should they choose to not call ``resume``).

Built atop the effect system, we support Lua-style coroutines as a library.

Others have used algebraic effects and handlers to tackle parsing, concurrency,
exceptions, ambient/implicit variables, and generators. These use cases could
all be handled by Foster's primitives. Effects are a relatively recent addition
to the language so not much code actually uses them yet.

One example which Foster cannot directly encode is nondeterministic choice, which
is usually implemented by having the effect handler call the ``resume`` function
multiple times. This is an intentional tradeoff: sacrificing some generality for
a faster implementation and a simpler mental model.


Interrupts
~~~~~~~~~~

The Foster compiler has a flag (``--optc-arg=-foster-insert-timer-checks``)
to insert flag checks, ensuring that a finite number
of instructions are executed between flag checks. A timer thread in the
runtime sets the flag every 16ms. Eventually, these timer interrupts should
cause a coroutine/effect yield, which will enable (nested) scheduling. For now,
the runtime just prints a message whenever the flag trips.


Types
~~~~~

Polymorphism
++++++++++++

Functions can be given polymorphic type annotations::

   foo :: forall (t:Type) { Array t => Int32 };
   foo = { a => arrayLength32 a };

Individual functions can also be made polymorphic without a separate type
annotation::

   foo = { forall t:Type, a : Array t => arrayLength32 a };

Unlike many languages, Foster uses a kind system to differentiate
between values which are guaranteed to be represented as a pointer,
and values which may or may not be pointer-sized.
The former have kind ``Boxed``, the latter have kind ``Type``.
The primary restriction is that when passing around polymorphic functions
in a higher-order way (that is, when using higher-rank polymorphism),
they must abstract over ``Boxed`` types, since we can provide only
a single compiled implementation and we can't control what type the
caller provides when instantiating the polymorphic function.

This restriction could be lifted by using intensional polymorphism.
I'm undecided on whether it's better to accept the restriction that
reflects an implementation constraint, or extend the implementation
(and add some complexity, and add a different sort of constraint,
in the form of limiting separate compilation)
to lift the constraint. The main issue where this comes up is
in monadic-style encodings, where it's kinda painful to be restricted
to only defining monads over boxed types.

One difference from traditional ML-like languages is that Foster does
not perform implicit quantification of types describing values.
Any polymorphism of values must be explicitly written (and thus
explicitly scoped).
However, Foster will perform implicit quantification of non-value
type parameters (e.g. for effects, and regions if/when we get 'em).

Foster allows explicit instantiation of polymorphic values,
the syntax for which (``:[t]``) echoes the syntax for array
indexing (``.[e]``).

Refinements
+++++++++++

Unlike most languages, we support refinement types, which are statically
checked using an SMT solver. Foster's approach, which merely propagates and
checks refinements, is much less ambitious than LiquidHaskell,
which seeks to infer refinements.

Here's a silly example, which shows that we can require the caller pass
only arrays of length 3::

    arrayLenInp3 :: { % aa3 : Array Int32 : prim_arrayLength aa3 ==Int64 3 => Int32 };
    arrayLenInp3 = { a3 => 0 };

    la = prim mach-array-literal 1 2 (opaquely_i32 3);
    la2 = prim mach-array-literal 1 (opaquely_i32 3);

    expect_i1 True;
    print_i1 (prim __COMPILES__ (arrayLenInp3 la));

    expect_i1 False;
    print_i1 (prim __COMPILES__ (arrayLenInp3 la2));

If ``T`` is a type, then ``% name : T : pred`` is a refined type
where the property ``pred`` (which can mention ``name``) holds of all values
which inhabit the type at runtime.

As you can see, the syntax could be improved.

Another silly example, demonstrating the connection between type annotations
and the variables affected by the annotation::

    expgt2 :: { % zz : Int32 : zz >UInt32 2 => Int32 };
    expgt2 = { yy =>
      prim assert-invariants (yy >=UInt32 1);
      0
    };

This uses a primitive to directly query the SMT solver;
if the SMT solver cannot show that the given property holds,
compilation fails.

Note that the SMT solver performed the following chain of reasoning:
``zz = yy``, and ``zz > 2``, therefore ``yy >= 1`` is true.

A less-silly example is in the Foster implementation of ``siphash``,
which uses the ``subscript-static`` primitive to perform array indexing
safely without runtime bounds checking.

Notes
-----

SMT checking can be slow, depending on what operations are used.
For example, reasoning about multiplication is much more intensive than other bitvector operations.
In some sense, we require explicit annotations from the programmer to help guide the SMT solver
through a vast and treacherous search space.

The Foster compiler caches checksums of queries that succeed.
Thus, in the common case, queries that have already been proven true do not need to be fed
to an SMT solver to be re-verified.
This eliminates the most expensive part of refinement type checking from the edit-compile cycle.

When an invariant or assertion cannot be proven, the compiler simply prints out the complete script
that could not be proven.
The programmer is basically on their own to reverse-engineer what missing constraint or invariant
is needed for the proof to go through.
I'm not aware of a robust method for determining missing invariants, but if you know of any, please
do let me know!

Examples
--------

SHA/extract-byte
~~~~~~~~~~~~~~~~

Sometimes adding a refinement necessitates cascading changes to propagate sufficient static information
to make the proof work. Other times, a single refinement is enough to "bridge the gap".
This example shows such a case.

When finalizing a SHA-256 hash, we must translate from an internal array of 32-bit words to an external
array of 8-bit words. The following line of code does so, using helper functions ``sv`` and ``s2`` to
map each output word to a byte within an internal word::

    newDArray0 32 { n => extract-byte-Int32 h.[s2 n] (sv n) };

    sv = { x => 3 -Int32 (x `bitand-Int32` 3) };

The ``extract-byte-Int32`` function requires that its second input---here, ``sv n``---be a valid byte identifier.
For a 32-bit number, there are only four valid byte identifiers: 0, 1, 2, and 3.
Rather than check this property dynamically, the ``extract-byte-Int32`` function requires that the caller discharge
a static proof of validity for any argument it passes.

The definition of ``sv`` does clearly satisfy this property: ``bitand x 3`` can only be a number from zero to 3,
and three minus such a number likewise falls within the same range.

Without a type annotation on ``sv``, the Foster compiler will not be able to satisfy the precondition of ``extract-byte``;
to do so would require inter-procedural reasoning.
However, things work if the programmer adds a type annotation with a constraint on the return value of ``sv``::

    sv :: { Int32 => % rv : Int32 : rv <UInt32 4 };

This annotation provides a clean division of labor for the compiler's static checking machinery:
the annotation can be checked against the function definition once, and then assumed at all other uses of ``sv``.
Conceptually, given a function of "size" N with M call sites,
we would otherwise have to potentially do N * M work finding the right property at each call site.
With an explicit annotation, we are faced instead with N + M work.

ldexp/scalbn
~~~~~~~~~~~~

Here is the C implementation of the standard library function ``scalbn`` (commonly used via ``ldexp``)
from `Musl <http://musl.libc.org/>`_:

.. code-block:: text

    double scalbn(double x, int n)
    {
        union {double f; uint64_t i;} u;
        double_t y = x;

        if (n > 1023) {
            y *= 0x1p1023;
            n -= 1023;
            if (n > 1023) {
                y *= 0x1p1023;
                n -= 1023;
                if (n > 1023)
                   n = 1023;
            }
        } else if (n < -1022) {
            /* make sure final n < -53 to avoid double
              rounding in the subnormal range */
            y *= 0x1p-1022 * 0x1p53;
            n += 1022 - 53;
            if (n < -1022) {
                y *= 0x1p-1022 * 0x1p53;
                n += 1022 - 53;
                if (n < -1022)
                    n = -1022;
            }
        }
        u.i = (uint64_t)(0x3ff+n)<<52;
        x = y * u.f;
        return x;
    }

Here is the equivalent code rendered in Foster::

    pow2-Float64 :: { Float64 => Int32 => Float64 };
    pow2-Float64 = { x => i =>
      times2tothe = { x : Float64 => n : Int32 =>
        pow2 = (0x3ff +Int64 zext_i64_to_i32 n) `bitshl-Int64` 52
                |> i64-as-f64;
        pow2 *f64 x
      };

      REC adjust-expt-down = { y : Float64 => n : Int32 => fin : Bool =>
        ny = y *f64 0x1.0p1023;
        nn = n -Int32     1023;

        case (fin, nn >SInt32 1023)
          of (_   , False) -> ny `times2tothe` nn
          of (True,  True) -> ny `times2tothe` 1023
          of (False, True) -> adjust-expt-down ny nn True
        end
      };

      REC adjust-expt-up = { y : Float64 => n : Int32 => fin : Bool =>
        // 1022 - 53 = 969
        ny = y *f64 0x1.0p-969;
        nn = n +Int32      969;

        case (fin, nn <SInt32 -1022)
          of (_   , False) -> ny `times2tothe` nn
          of (True,  True) -> ny `times2tothe` -1022
          of (False, True) -> adjust-expt-up ny nn True
        end
      };

      case ()
        of _ if i >SInt32 1023  -> adjust-expt-down x i False
        of _ if i <SInt32 -1022 -> adjust-expt-up   x i False
        of _ -> x `times2tothe` i
      end
    };

A few differences to note:

* The Foster code is slightly longer and more verbose -- 31 lines of code versus 27.
* In the C code, the code to detect and handle special cases is intertwined;
  Foster uses local helper functions to separate them.
* The local helper functions will be boiled away by the compiler. How do we know this will happen?
  The ``adjust-`` functions have only one non-tail-recursive usage.
  This means they can be eliminated via contification.
  The ``times2tothe`` function only occurs in tail position, which means its continuation is static
  and it can be contified. After the ``adjust-`` functions are dealt with,
  this other helper will be eligible for elimination.
* In the C code, mutation can alter the values used by the main operation;
  in the Foster code, mutation is replaced by explicit naming of functions and altered values.
* The Foster code is less repetitious; it contains three fewer occurrences of ``1023``.
* Whereas C uses an generic unsafe primitive (``union``) to convert between
  unsigned integer bitpatterns and floating-point values,
  Foster provides a safe specialized primitive.

C2Foster
--------

One bit of cool (and still developing) infrastructure is a program called ``c2foster``
to translate C code into Foster code.

For example, given the following C code::

    #include <stdio.h>

    int foo(int x) { return x; }
    int main() {
      printf("%d\n", foo(3 << 3));
    }

we automatically produce the following Foster code::

    snafuinclude C2F "c2f";
    foo = { x : Int32 => x };

    main = { print_i32 (foo (bitshl-Int32 3 3)) };

A script called ``csmith-minimal.sh`` directs `Csmith <https://embed.cs.utah.edu/csmith/>`_
to generate random C programs in a restricted subset of C, which can be fed into ``c2foster``.
This is useful to stress test certain parts of the compiler.

Implementation
--------------

Interpretation
~~~~~~~~~~~~~~

There is a small-step interpreter, available via the ``--interpret`` flag.
It's mainly intended as a reference semantics, not a day-to-day REPL or
anything like that. It's likely somewhat bitrotted at this point.

Compilation
~~~~~~~~~~~

The Foster middle-end does some high-level optimizations like contification
and inlining. The LLVM backend then does further work.

The following small Foster program::

    main = {
      REC loop = { x =>
        case x
          of 0 -> x
          of _ -> loop (x -Int32 1)
        end
      };
      print_i32 (loop (opaquely_i32 3));
    };


produces the following lightly-optimized LLVM IR, in which the local function
has become a set of local basic blocks::

    define void @foster__main() #2 gc "fostergc" {
    entry:
      %".x!580" = call i32 @opaquely_i32(i32 3)                   ; #uses = 1	; i32
      br label %contified_postalloca.L591

    contified_postalloca.L591:                        ; preds = %case_arm.L594, %entry
      %"scrut.occ!615" = phi i32 [ %".x!580", %entry ], [ %".x!578", %case_arm.L594 ] ; #uses = 3	; i32
      %cond = icmp eq i32 %"scrut.occ!615", 0                     ; #uses = 1	; i1
      br i1 %cond, label %case_arm.L593, label %case_arm.L594

    case_arm.L594:                                    ; preds = %contified_postalloca.L591
      %".x!578" = sub i32 %"scrut.occ!615", 1                     ; #uses = 1	; i32
      br label %contified_postalloca.L591

    case_arm.L593:                                    ; preds = %contified_postalloca.L591
      call void @print_i32(i32 %"scrut.occ!615"), !willnotgc !4
      ret void
    }

which gets translated to this assembly code (use the ``--asm`` flag)::

    foster__main:                           # @foster__main
    # BB#0:                                 # %entry
            pushl	%ebp
            movl	%esp, %ebp
            subl	$24, %esp
            movl	$3, %eax
            movl	$3, (%esp)
            movl	%eax, -4(%ebp)          # 4-byte Spill
            calll	opaquely_i32
            movl	%eax, -8(%ebp)          # 4-byte Spill
    .LBB14_1:                               # %contified_postalloca.L591
                                            # =>This Inner Loop Header: Depth=1
            movl	-8(%ebp), %eax          # 4-byte Reload
            cmpl	$0, %eax
            movl	%eax, -12(%ebp)         # 4-byte Spill
            je	.LBB14_3
    # BB#2:                                 # %case_arm.L594
                                            #   in Loop: Header=BB14_1 Depth=1
            movl	-12(%ebp), %eax         # 4-byte Reload
            subl	$1, %eax
            movl	%eax, -8(%ebp)          # 4-byte Spill
            jmp	.LBB14_1
    .LBB14_3:                               # %case_arm.L593
            movl	-12(%ebp), %eax         # 4-byte Reload
            movl	%eax, (%esp)
            calll	print_i32
            addl	$24, %esp
            popl	%ebp
            retl

LLVM did some strange register scheduling in this case, spilling and restoring
``%eax`` across the loop boundary. If we enable
``-O2`` level optimization, using the ``--backend-optimize`` flag to
``runfoster``, LLVM simply eliminates the loop.

Optimizations
~~~~~~~~~~~~~

One interesting backend optimization: we turn (the LLVM equivalent of C)
code like::

       (((T)buf[0]) << (0 * sizeof(buf[0])))
     | (((T)buf[1]) << (1 * sizeof(buf[0])))
     | (((T)buf[2]) << (2 * sizeof(buf[0])))
     | (((T)buf[3]) << (3 * sizeof(buf[0])))

into::

      ((T*)buf)[0]

(on little-endian architectures, of course.)

Benchmarking Infrastructure
~~~~~~~~~~~~~~~~~~~~~~~~~~~

* TODO cover ``bench-all.py``, ``bench-diff.py``, and ``bench-ize.py``.

    bench-ize.py data/2013-08-09@11.46.53/all_timings.json --overview
    bench-ize.py data/2013-08-09@11.46.53/all_timings.json --test fannkuchredux
    open bench-ized.html

Standard Library
~~~~~~~~~~~~~~~~

A few random bits and pieces:

* Bignum library, ported from libtommath (partial)
* sha256, siphash, and few non-cryptographic PRNGs ported from reference C implementations
* Finger trees, maps, sets, and sequences, ported from Haskell
* Various purely functional data structures, ported from Okasaki
* Lazy values
* A subset of QuickCheck
* A few benchmarks ported from the Language Shootout Benchmarking Game.
* A partial implementation of a TCP stack, in test/speed/foster-posix/foster-net
* A port of a UTF-8 decoder, which uses a dash of refinement types,
  in test/speed/micro/utf8-decode

Unimplemented Bits
------------------

* Mutability tracking for arrays
* Control over aliasing
* (Possibly) regions for Ref cells and/or other datatypes
* Full story on boxed vs unboxed types
* Module system
* Non-trivial use of effects
* Any form of JIT compilation
