Dive Into Foster
================

Current Status
--------------

Hello World
~~~~~~~~~~~

Here's the Foster version of 'Hello, World'::

    snafuinclude Prelude "prelude";

    main = {
      print_text "Hello, World";
    };

The syntax for importing code is a temporary placeholder, mirroring the fact
that the implementation (essentially ``#include``) is a temporary hack.

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

Operators
~~~~~~~~~

Unlike C, there's no overloading or implicit conversion, so ``+Int32``
is a separate function from ``+Int64``. Also, signedness is a property of
operations rather than values: there are separate
``>UInt32`` and ``>SInt32`` primitives, but no separate add/mul/etc functions,
which produce identical bit values for "signed" and "unsigned" values.

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
which are Haskell/ML style: ``fn arg1 arg2``. Unlike those languages,
functions aren't curried. That is, there's a distinction between a function
that takes two arguments, and one that takes one argument and returns a function
that takes another argument. Calling a function that returns a function
must be ``(fn arg1) arg2``.

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

Other expressions include numbers (for now: double precision float or
8 to 64-bit integer), strings (Python-like syntax: single or double quotes,
in single or triple-pair flavors; :doc:`strings` can be prefixed with ``r`` to
disable escaping, or ``b`` to produce bytestrings ``(Array Int8)`` instead
of ``Text``; there is no primitive character type), pattern matches
``case e of p1 -> e1 of p2 -> e2 end``, conditionals ``if a then b else c end``,
tuples ``(a, b, c)``, and booleans ``True``/``False``.

Once upon a time, numbers had Fortress-style radix suffixes (like ``8FFF_16``)
but now we use regular hex/binary prefix syntax (``0b1101``). Numbers can have
embedded backticks to provide visual separation: ``0b`1110`1110``.

Pattern matches can have guards, and non-binding or-patterns are supported::

    // Evaluates to 200
    case (1, 2)
      of (a, 2) if a ==Int32 2 -> 100
      of  (2, 3)
       or (1, 2) -> 200
      of _ -> 300
    end

Pattern matching doesn't currently support arrays.

One interesting expression form is ``(__COMPILES__ e)``,
which evaluates (at compile time) to a boolean value reflecting whether
the provided expression was well-typed.
This can be useful to make sure that "improper" usage of an API
is being prevented by the type system.

.. note::

  Pedantic note: ``__COMPILES__`` does not undo the effects of type checking
  its argument; thus, by modifying unification variables, adding a
  ``__COMPILES__`` primitive to working code can cause other code to fail
  to type check properly.

Some expressions are represented with primitive functions rather than
dedicated syntax. For example, instead of Python-style ``[1, 2, 3]``
for arrays, we get by with ``prim mach-array-literal 1 2 3``.
It's ugly but it retains flexibility.
Better syntax will likely come in the future, but a big question is:
for what data structures?


Statements
~~~~~~~~~~

Within a function body: bindings or expressions. Bindings of recursive functions
use a ``REC`` marker. Destructuring binds are supported for tuples::

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
in patterns and data type definitions (but not for e.g. function calls).


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
In this example, the compiler would generate symbols with the following types:

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
all be handled by Foster's primitives.

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
cause a coroutine yield, which will enable (nested) scheduling. For now,
the runtime just prints a message whenever the flag trips.


Types
~~~~~

Polymorphism
************

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

Effects
*******

We have (some) support for Koka-style effects. In this example, we verify
that passing a function which has the Net and Console effects cannot be
passed if the caller allows only the Console effect, but is allowed if
the caller allows Console and Net::

    expect_i1 False;
    print_i1 (__COMPILES__ {
            chk : { { () @(Console)     } => () } =>
            f1  :   { () @(Net,Console) }         =>
            chk f1;
          });

    expect_i1 True;
    print_i1 (__COMPILES__ {
            chk : { { () @(Console,Net) } => () } =>
            f2 :    { () @(Net,Console) }         =>
            chk f2;
          });

However, the standard library does not yet make use of effect types.
At the moment, they're only used for coroutines, to track what type
the coroutine is going to yield. Any function called by a coroutine
is allowed to yield a value (that's what it means to support stackful
coroutines).

Refinements
***********

Unlike most languages, we support refinement types, which are statically
checked using an SMT solver.

Here's a silly example, which shows that we can require the caller pass
only arrays of length 3::

    arrayLenInp3 :: { % aa3 : Array Int32 : prim_arrayLength aa3 ==Int64 3 => Int32 };
    arrayLenInp3 = { a3 => 0 };

    la = prim mach-array-literal 1 2 (opaquely_i32 3);
    la2 = prim mach-array-literal 1 (opaquely_i32 3);

    expect_i1 True;
    print_i1 (__COMPILES__ arrayLenInp3 la);

    expect_i1 False;
    print_i1 (__COMPILES__ arrayLenInp3 la2);

Another silly example, demonstrating the connection between type annotations
and the variables affected by the annotation::

    expgt2 :: { % zz : Int32 : zz >UInt32 2 => Int32 };
    expgt2 = { yy =>
      prim assert-invariants (yy >=UInt32 1);
      0
    };

Note that the SMT solver performed the following chain of reasoning:
``zz = yy``, and ``zz > 2``, therefore ``yy >= 1`` is true.

A less-silly example is in the Foster implementation of ``siphash``,
which uses the ``subscript-static`` primitive to perform array indexing
safely without runtime bounds checking.

C2Foster
--------

One bit of developing-but-cool infrastructure is a program to translate
C code into Foster code. ``csmith-minimal.sh`` generates random C programs
(in a restricted subset of C), which ``c2foster`` then translates into
Foster code.

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
* sha256, siphash, xorshift ported from reference C implementations
* Finger trees, maps, sets, and sequences, ported from Haskell
* Various purely functional data structures, ported from Okasaki
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

Vision
------

* ML-style type safety provides a solid foundation for a reasonable language.
* For reasons of both maintainability and security, we'd also like to
  track and restrict the effects of executing a given piece of code,
  thus effect typing.
* Given effect typing, something like extensible effects provides a unified
  mechanism for language-based interpositioning.
* Coroutines serve as a behind-the-scenes implementation mechanism for
  extensible effects, and also for an independent, hugely useful,
  in-front-of-the-scenes language mechanism.

