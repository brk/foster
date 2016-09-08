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


To run an individual file, use ``runfoster``::

    :2016-09-07 16:06:09 ~/foster/_obj/ $ cat scratchpad.foster
    snafuinclude Prelude "prelude";
    main = {
      print_text "Hello, world!";
    };
    :2016-09-07 16:06:11 ~/foster/_obj/ $ runfoster scratchpad.foster
    Hello, world!

Syntax
~~~~~~

Files are a collection of top-level function definitions (for now, there are
no global constants or arrays). Functions can have type annotations::

    foo :: { Int32 => Int32 };
    foo = { a => b => a +Int32 b };

You can also put type annotations on individual parameters::

    foo = { a : Int32 => b => a +Int32 b };

Type inference determines that the ``b`` parameter and return type of ``foo``
are both ``Int32`` in this instance.

Like in Haskell, you can use regular words as infix operators with backticks,
and turn operators into "regular" names with parens::

    // (foo 20 3) will print 123
    foo = { x => y =>
      bar = { a => b => (((+Int32) a b) +Int32 100 };
      x `bar` y
    };

Obviously, ``//`` is a line comment. Less obviously, ``/* ... */`` is a
nesting block comment.

Operators
~~~~~~~~~

Unlike C, there's no overloading or implicit conversion, so ``+Int32``
is a separate function from ``+Int64``. Also, signedness is a property of
(comparison) operations rather than values: there are separate
``>UInt32`` and ``>SInt32`` functions, but no separate add/mul/etc functions.

There are explicit checked add/sub/mul operators,
which do come in signed and unsigned variants:
``+ucInt32``, ``*scInt64``, etc.

Bitwise operators are spelled like ``bitand-Int32``. The operators are
``bitand``, ``bitor``, ``bitxor``, ``bitshl``, ``bitlshr``, ``bitashr``, and ``bitnot``.
There's also ``ctlz`` and ``ctpop``.

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
``arg2 |> fn arg1``.

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

Some expressions are represented with primitive functions rather than
dedicated syntax. For example, instead of Python-style ``[1, 2, 3]``
for arrays, we get by with ``prim mach-array-literal 1 2 3``.
It's ugly but it retains flexibility.

Coroutines
~~~~~~~~~~

Foster supports Lua-style stackful coroutines.
The following code::

    co = coro_create { x : Int32 =>
           print_i32 x;
           y = coro_yield 6666;
           coro_yield y;
           9999
    };

    print_i32 (coro_invoke co 10);
    print_i32 (coro_invoke co 20);
    print_i32 (coro_invoke co 30);


will print out::

    10
    6666
    20
    9999

Interrupts
~~~~~~~~~~

The Foster compiler has a flag (``--optc-arg=-foster-insert-timer-checks``)
to insert flag checks, ensuring that a finite number
of instructions are executed between flag checks. A timer thread in the
runtime sets the flag every 16ms. Eventually, these timer interrupts should
cause a coroutine yield, which will enable (nested) scheduling. For now,
the runtime just prints a message whenever the flag trips.


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

There is a small-step interpreter, available via the ``--interpret`` flag.(
It's mainly intended as a reference semantics, not a day-to-day REPL or
anything like that.

Compilation
~~~~~~~~~~~

The Foster middle-end does some high-level optimizations like contification,
inlining, and GC root analysis. The LLVM backend then does further work.

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

Bare-Metal Mode
~~~~~~~~~~~~~~~

There's a ``--standalone`` flag for the compiler
(and a ``fosterc-standalone`` driver script) which disables linking
with the runtime. This could, in theory, be useful for creating
very low-level code, such as the implementation of an operating system.

However, I haven't done much with it yet, mainly because I think it
would be worth extending the benefits of effects and handlers to
standalone code, as much as possible, and I'm not sure of the right
way of doing so.

One way of going about it is to have a layered runtime, such that
only a very very small amount of code is truly zero-runtime,
and most code can assume at least coroutine primitives.
A different approach would be to have an alternate implementation
of certain primitive effects in standalone mode, probably not involving
the "regular" implementation of coroutines at all.

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
* Effect handlers
* Monadic effect translation
* Any form of JIT compilation
* A sophisticated garbage collector

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
*

