Compiler Overview
==================

The compiler was originally a monolithic C++ binary.
It is now a separate front-end, middle-end, and back-end,
which communicate via protocol buffers.

The front-end is written in C++, and uses ANTLR and LLVM
to turn text strings into parse trees, which it then
massages into AST nodes.

.. note::
    If we ever allow modules to export precedence or other
    syntax rules, then constructing a properly structured
    AST requires being able to get information that depends
    on the contents of other modules.
    The minimal information needed is syntax exports and
    module dependencies.
    In practice, it will also mean that parsing requires
    searching input paths to find module information.

The middle-end is written in Haskell. It takes a module's
AST node and performs resolution (with hardcoded types for
standard library functions) and type checking. Eventually,
type checking should be performed on SCCs of modules.

The back-end is written in C++. The primary advantage of
using C++ rather than Haskell for lowering to LLVM is that
we can use custom LLVM IR passes, as well as our GC plugin.
LLVM provides some support for loadable modules, which enables
passes to be dynamically loaded into standard LLVM tools like
``opt`` and ``llc``. Unfortunately, that functionality is not
supported on Windows, and will not be in the forseeable future.
Thus, we must in to some degree write a copy of ``opt`` and/or
``llc`` which statically link in our plugin and passes.
Currently, we have a ``fosterlower`` binary, which converts
protobufs with a close-to-LLVM representation, and outputs
linked LLVM with initial peephole optimizations. There is a
second ``fosteroptc`` binary which optimizes the final program
and emits native assembly (in the future, this will likely
output a binary directly, saving us at most 5% in compilation time).

Possible choices for generation of LLVM IR:

  * Have C++ convert custom IR from protobuf to LLVM
  * Have Haskell generate LLVM via text string pasting
  * Have Haskell generate LLVM-isomorphic protocol buffers

.. ::
    #. Resolution: compute fully-qualified versions of all names.
            At this stage we need to have export information from imported modules.
            This is where we need to build the symbol table.
    #. Typechecking / type inference.
        At the end of this pass, we can emit a module interface AST
        in protobuf format, which can be used directly (in place of
        re-parsing from a string) by other modules importing this module.
    #. Closure Conversion
    #. Code Generation

.. ::
        Module.Submodule.function
        object.subobject.field
        object.subobject.function
        Type.anything?

-------

Module dependency tracking could be done by either the
front-end, middle-end, or driver.
It requires a list of input paths to search.

If parsing is responsible for
collecting and recursively parsing imported modules, then the output is a list
of ``(Either (Protobuf SugaryAST) (Protobuf TypecheckedAST)`` depending on
whether the imported module has been compiled more recently than it was
modified, and the protobufs in either case should embed each module's full
dependency graph. Otherwise, parsing has a much simpler signature
(``String -> Protobuf SugaryAST``), protobufs need only include direct import
information, and sema is responsible for recursively ensuring that all imported
modules are parsed, and for building the import graph from ASTs to determine
the set of recursively imported modules.

.. ::
    Conceptually, though, there are three nominally independent pieces:

    #. Parsing :: ``(String , [InputPath]) -> [Protobuf SugaryAST]``
    #. Type checking :: ``[Protobuf SugaryAST] -> Either (Protobuf TypecheckedAST) (Protobuf CFG , [ImportedModules])``
    #. Code Generation :: ``(Protobuf CFG, [ImportedModules]) -> LLVM IR Module``



Parse Trees
-----------

In order to capture more detailed source token information,
we insert a filter in the ANTLR parser object before starting a
top-level parse. The filter associates token boundaries with ANTLR
parse tree objects. Unfortunately the assocation must be done in a
statically-accessible map. Therefore parsing must be done in a dedicated
parsing context.

A parse tree is a simple tree-encoded representation of an input string.
Parse trees themselves do not have proper semantics: for example, binary
operators corresond in structure to their source ordering, not their
relative precedences.

AST Building
------------

AST building performs an operator precedence post-processing pass to
determine the proper structure of operators.

Currently modules are restricted to topologically sorted imports.
Diatchki, Jones, and Hallgren present a fairly straightforward approach
for handling SCCs of mutually-recursive modules via fixed-point computation
of exports: http://ogi.altocumulus.org/~hallgren/hsmod/Description.pdf
In this case, rather than compiling one module at a time, the compiler
would process one SCC at a time.

Future Plans
~~~~~~~~~~~~

A sketch of my current thoughts on how to structure the compilation
system, especially with regards to separate compilation of modules:

Four components: driver, parser (front-end), middle-end (type checker),
and back-end (LLVM codegen).

The driver gets a command to compile some file ``Foo.foster``.
If the driver cannot find an up-to-date AST for the given file,
a request is sent to the front-end, which must parse
from a string to a parse tree, and then
post-process the parse tree to get an abstract syntax tree.
The front-end returns to the driver an abstract syntax tree.
This AST contains a list of the modules that Foo imports (recursively?).
The driver can then (in parallel) obtain ASTs for ``Foo``'s
dependencies, transitively.

Some of the imported modules may have already been compiled, in which case
their ASTs can be used directly; other modules will not have been
compiled, in which case they must be compiled before the module(s) that
import them may undergo codegen.

Because the parser does not "peek" at imported modules, the ASTs produced
by the parser do not contain resolved symbols.

So, at this point, the driver has module Foo's dependency graph on other
modules. The driver can process the SCCs of the graph in topologically sorted
order. Note, though, that a SCC of N modules produces N compiled modules as
output, not one "supermodule." The SCC is needed to compute the fixed-point
of the import/export signatures of each module. Once those have been computed,
compilation proceeds independently for each module in the SCC.

Once a module has been typechecked, it proceeds to the backend, which generates
a LLVM ``Module``. The ``Module`` can be immediately cleaned up with custom LLVM passes,
before being written to disk.

In order to reduce recompilation burden, ``Module``\s are not immediately linked
with the ``Module``\s they import. Instead, they simply use LLVM declarations to
reference the symbols they import.

Once LLVM ``Module``\s have been generated for each module imported by Foo, the
final stages of the driver pipeline take over:
  * The entire collection of ``Module``\s are linked and (re-)optimized
  * then spit out to a ``.s`` and/or a ``.o``
  * and finally linked to any native libraries (``.a``/``.o``/``.lib``/``.so``)
  * producing a native executable


.. Who is responsible for searching the file system to find module impls?
.. etc

-----

It remains to be seen whether the middle-end and back-end should be strongly
separated or not. My current thought is that there's no inherent benefit to
separation, except that the middle-end seems easiest to implement in Haskell
whereas the back-end seems easiest to implement in C++.

The back-end may actually be several distinct pieces:
  * AST or CFG to LLVM ``Module`` (may require some custom LLVM passes)
  * ``Module`` to asm/obj (requires GC plugin)
  * Linker + optimizer: could be separate binary or could reuse ``llvm-ld``
    and ``opt``.



LLVM Bindings
-------------

LLVM has bindings for Haskell. However, there are a few separate problems
with using non-native LLVM bindings.

First, those bindings are not nearly
as rich as the native C++ API. This makes it more difficult to generate
e.g. debug information.

Second, the Haskell LLVM bindings link against the system version of LLVM,
whereas Foster generally builds with a separate LLVM install.

Third, lowering protobufs to LLVM IR currently requires loading some
standard library bitcode files. Ensuring that the type checker can operate
independently is important for modularity.

The design of the backend does anticipate self-hosting, however:
Foster-specific LLVM passes are encapsulated in a LLVM-to-LLVM binary
called ``fosteroptc``, which is distinct from the ``fosterlower`` binary
that converts typechecked protobufs to LLVM IR.


Random Timing Notes
-------------------

With debug info enabled for libfoster::

    013 K .ll -(107 ms)-> 337 K  preopt.bc (fosterlower) (23 ms linking, 40 ms reading, 23 ms dumping bitcode)
    337 K .bc -(314 ms)-> 2.2 MB out.s     (fosteroptc) (39 ms reading, 255 ms llc, 4 ms opt)
    2.2 M  .s -( 46 ms)-> 196 K  out.o     (gcc/as)
    196 K  .o -( 59 ms)-> 1.9 M  a.out     (gcc/ld)

Without debug info enabled for libfoster::

    013 K .ll -( 28 ms)->  50 K  preopt.bc (fosterlower) ( 1 ms linking,  6 ms reading,  4 ms dumping bitcode)
     50 K .bc -(230 ms)-> 266 K  out.s     (fosteroptc) ( 7 ms reading, 213 ms llc, 1 ms opt)
    266 K  .s -( 17 ms)->  37 K  out.o     (gcc/as)
     36 K  .o -( 57 ms)-> 1.8 M  a.out     (gcc/ld)

By disabling debug info, compilation time per-module drops from 565 ms by 170 ms, to 389 ms.
Time for ``ctest -V`` similarly drops from 16 s to 11 s.

By making the 2.2 MB ``libchromium_base`` library linked dynamically instead of statically,
final binary sizes are 1.5 MB smaller, and link time drops from 57 ms to 27 ms. Time for ``ctest -V``
dropped by 10% overall.
