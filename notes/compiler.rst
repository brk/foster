Compiler Overview
==================

The compiler was originally a monolithic C++ binary.
It is now a separate front-end, middle-end, and back-end,
which communicate via protocol buffers.

The front-end is written in C++, and uses ANTLR
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

The middle-end is written in Haskell. It takes a module's AST
and performs resolution (with hardcoded types for standard
library functions), type checking, k-normalization,
monomorphization, pattern match compilation, and closure
conversion. Eventually, type checking should be performed on
SCCs of modules.

The back-end is written in C++. The primary advantages of
using C++ rather than Haskell for lowering to LLVM are:

  * We can use custom LLVM IR passes.
  * We can use a custom GC plugin.
  * It's easier to link against our standard library,
    especially when we don't know the types of certain symbols
    in advance.
  * It seems easier to do GC metadata & type maps this way.

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
and emits native object code or assembly.

Possible choices for generation of LLVM IR:

  * Have C++ convert custom IR from protobuf to LLVM (currently done)
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

Direct Style, CPS, & CFG
------------------------

The interface between the middle-end and back-end has evolved
over time:

* ...?
* Nested expressions gave way to k-normalized forms.
  This makes GC-root-safety more explicit and easier to enforce.
  In particular, because operand values have trivial codegen,
  there is no chance to forget to stick an intermediate value in
  a stack slot. Before this change, function calls and other
  similar constructs needed an awkward two-phase codegen, where
  the first phase would codegen all the (pointerly) arg expressions into
  stack slots, and the second phase would load the pointers out
  of those stack slots. This dance was required in case a GC was
  triggered while codegenning argument i > 0.

  Another benefit was that small-step interpretation also became
  simpler.
* Control flow constructs, like ``if``, were initially
  expressions when fed into the backend. The backend was then
  responsible for building the associated control flow graph. To
  avoid phi nodes, the backend would introduce a stack slot for
  each if expression; the final value from each branch would be
  stored in the stack slot, and the overall value of the ``if``
  was the result of a load from the slot. LLVM's ``mem2reg``
  pass could then be left to build phi nodes if it so saw fit.

  When an explicit (stack/heap) allocation construct was added
  to the backend's input language, responsibility for creating,
  storing, and loading stack slots for ``if`` nodes passed to the
  middle-end.
* Case expressions (or, more precisely, the decision trees
  derived from same) are trickier, both in their initial
  implementation and their evolution, because they combine
  control flow with value binding.

  Originally, compilation of a case involved allocating
  a "return value" slot, recursively generating code for the
  decision tree(s), and finishing with a load from the stack
  slot. Each decision tree was either a fail node, a leaf, or
  a switch.

  A switch would inspect a particular subterm of the scrutinee,
  and compute a small integer tag for the constructor (or the
  value itself, for integers). Each branch would codegen
  a decision tree starting in a separate basic block, thus
  building a diamond-shaped control flow subgraph::

              [  ...   ]
              [ switch ]
              /   |    \
           {...} {.}  {...}
           {...} {.}  {...}
              \   |    /
               [ cont. ]

  Codegen of decision tree leaves (expressions) was where the
  magic really happened. Each leaf would have an associated list
  of bindings, giving names to subterms of the scrutinee. So the
  backend would add those names to its symbol table, emit the
  leaf expression, and then remove the names from the symbol
  table.

  Consider an example with nested pattern matching::

     case ((1, 2), (3, (4, 5)))
       of ((x, y), (z, (5, q))) -> 5
       of ((a, b), (4, qq    )) -> 6
       of ((c, 7), (3, (4, 5))) -> 7
       of ((8, d), (3, (4, 5))) -> 8
       of (xy, zz) -> 123
       of xyzz -> 1234
     end;

  Pattern match compilation produces a CFG with 70 nodes and 96 edges
  (this is in hg rev fd7a6df9ef17, from nested-tuple-patterns).

  Several separate problems here:

    * The first literal tested is 8. If is mtaches, we go on and test many
      of the other subterms, completely unneccessarily. This amounts to an
      unneeded doubling of the CFG.

    * The decision tree for the above case analysis contains 28 leaf nodes,
      even though there should only be 6 actual leaves.
      zz, for example, is given 10 different
      stack slots, all of which are only ever stored into once! This is
      because there are 10 different copies of the ``-> 123`` branch.
      Only two copies of the ``-> 7`` branch, though.

--------------------------

  **With CFGs** the situation becomes more complicated. In particular, if we
  maintain a pure CFG representation, we lose the ability to scope the variables
  bound in decision tree leaves. Given uniqueness of binders, one
  straightforward (but not very elegant) solution would be to lift all the
  bindings to the "top level" of the function. This matches the eventual form
  of the generated LLVM IR, but it's rather ugly because it requires collecting
  all the binding information from the (switch terminators in the) CFG before
  actually codegenning the CFG itself. It also relies on the stack slots to
  provide a layer of indirection between the subterm values and the binding
  names.

  The solution adopted by CPS-style languages is to provide explicit binders
  on basic blocks, in the same way that functions get binders. This, in turn,
  works because CPS blocks are lexically nested, unlike CFG blocks, which are
  (depending on perspective) either a flat list or a graph.

  One hacky solution would be to have switch nodes have nested *blocks* instead
  of pointers to blocks. But that's very ugly.

  A better solution is to simply make the order of code generation in blocks
  match the order of execution through blocks. Instead of codegenning blocks
  by walking through a flat vector, perform a DFS (or, since we have unique
  names, a BFS would also work). Assuming the CFG is well formed, we'll never
  generate a reference to an out-of-scope variable. If the CFG isn't well
  formed, the error will be caught by LLVM, so it doesn't make sense for us to
  check explicitly.


K-Normalization and Let-Flattening
----------------------------------

Probably easiest to show the effect of k-normalization
on a complete binary let-tree by example::

    ├─AnnLetVar    x!0 :: ()
    │ ├─AnnLetVar    x!1 :: ()
    │ │ ├─AnnLetVar    x!2 :: ()
    │ │ │ ├─AnnLetVar    x!3 :: ()
    │ │ │ │ ├─AnnLetVar    x!4 :: ()
    │ │ │ │ │ ├─AnnVar       b!5 :: ()
    │ │ │ │ │ └─AnnVar       n!6 :: ()
    │ │ │ │ └─AnnLetVar    x!7 :: ()
    │ │ │ │   ├─AnnVar       b!8 :: ()
    │ │ │ │   └─AnnVar       n!9 :: ()
    │ │ │ └─AnnLetVar    x!10 :: ()
    │ │ │   ├─AnnLetVar    x!11 :: ()
    │ │ │   │ ├─AnnVar       b!12 :: ()
    │ │ │   │ └─AnnVar       n!13 :: ()
    │ │ │   └─AnnLetVar    x!14 :: ()
    │ │ │     ├─AnnVar       b!15 :: ()
    │ │ │     └─AnnVar       n!16 :: ()
    │ │ └─AnnLetVar    x!17 :: ()
    │ │   ├─AnnLetVar    x!18 :: ()
    │ │   │ ├─AnnLetVar    x!19 :: ()
    │ │   │ │ ├─AnnVar       b!20 :: ()
    │ │   │ │ └─AnnVar       n!21 :: ()
    │ │   │ └─AnnLetVar    x!22 :: ()
    │ │   │   ├─AnnVar       b!23 :: ()
    │ │   │   └─AnnVar       n!24 :: ()
    │ │   └─AnnLetVar    x!25 :: ()
    │ │     ├─AnnLetVar    x!26 :: ()
    │ │     │ ├─AnnVar       b!27 :: ()
    │ │     │ └─AnnVar       n!28 :: ()
    │ │     └─AnnLetVar    x!29 :: ()
    │ │       ├─AnnVar       b!30 :: ()
    │ │       └─AnnVar       n!31 :: ()
    │ └─AnnLetVar    x!32 :: ()
    │   ├─AnnLetVar    x!33 :: ()
    │   │ ├─AnnLetVar    x!34 :: ()
    │   │ │ ├─AnnLetVar    x!35 :: ()
    │   │ │ │ ├─AnnVar       b!36 :: ()
    │   │ │ │ └─AnnVar       n!37 :: ()
    │   │ │ └─AnnLetVar    x!38 :: ()
    │   │ │   ├─AnnVar       b!39 :: ()
    │   │ │   └─AnnVar       n!40 :: ()
    │   │ └─AnnLetVar    x!41 :: ()
    │   │   ├─AnnLetVar    x!42 :: ()
    │   │   │ ├─AnnVar       b!43 :: ()
    │   │   │ └─AnnVar       n!44 :: ()
    │   │   └─AnnLetVar    x!45 :: ()
    │   │     ├─AnnVar       b!46 :: ()
    │   │     └─AnnVar       n!47 :: ()
    │   └─AnnLetVar    x!48 :: ()
    │     ├─AnnLetVar    x!49 :: ()
    │     │ ├─AnnLetVar    x!50 :: ()
    │     │ │ ├─AnnVar       b!51 :: ()
    │     │ │ └─AnnVar       n!52 :: ()
    │     │ └─AnnLetVar    x!53 :: ()
    │     │   ├─AnnVar       b!54 :: ()
    │     │   └─AnnVar       n!55 :: ()
    │     └─AnnLetVar    x!56 :: ()
    │       ├─AnnLetVar    x!57 :: ()
    │       │ ├─AnnVar       b!58 :: ()
    │       │ └─AnnVar       n!59 :: ()
    │       └─AnnLetVar    x!60 :: ()
    │         ├─AnnVar       b!61 :: ()
    │         └─AnnVar       n!62 :: ()
    ├─KNLetVal    x!4 :: () = ... in ...
    │ ├─KNVar(Local):   b!5 :: ()
    │ └─KNLetVal    x!3 :: () = ... in ...
    │   ├─KNVar(Local):   n!6 :: ()
    │   └─KNLetVal    x!7 :: () = ... in ...
    │     ├─KNVar(Local):   b!8 :: ()
    │     └─KNLetVal    x!2 :: () = ... in ...
    │       ├─KNVar(Local):   n!9 :: ()
    │       └─KNLetVal    x!11 :: () = ... in ...
    │         ├─KNVar(Local):   b!12 :: ()
    │         └─KNLetVal    x!10 :: () = ... in ...
    │           ├─KNVar(Local):   n!13 :: ()
    │           └─KNLetVal    x!14 :: () = ... in ...
    │             ├─KNVar(Local):   b!15 :: ()
    │             └─KNLetVal    x!1 :: () = ... in ...
    │               ├─KNVar(Local):   n!16 :: ()
    │               └─KNLetVal    x!19 :: () = ... in ...
    │                 ├─KNVar(Local):   b!20 :: ()
    │                 └─KNLetVal    x!18 :: () = ... in ...
    │                   ├─KNVar(Local):   n!21 :: ()
    │                   └─KNLetVal    x!22 :: () = ... in ...
    │                     ├─KNVar(Local):   b!23 :: ()
    │                     └─KNLetVal    x!17 :: () = ... in ...
    │                       ├─KNVar(Local):   n!24 :: ()
    │                       └─KNLetVal    x!26 :: () = ... in ...
    │                         ├─KNVar(Local):   b!27 :: ()
    │                         └─KNLetVal    x!25 :: () = ... in ...
    │                           ├─KNVar(Local):   n!28 :: ()
    │                           └─KNLetVal    x!29 :: () = ... in ...
    │                             ├─KNVar(Local):   b!30 :: ()
    │                             └─KNLetVal    x!0 :: () = ... in ...
    │                               ├─KNVar(Local):   n!31 :: ()
    │                               └─KNLetVal    x!35 :: () = ... in ...
    │                                 ├─KNVar(Local):   b!36 :: ()
    │                                 └─KNLetVal    x!34 :: () = ... in ...
    │                                   ├─KNVar(Local):   n!37 :: ()
    │                                   └─KNLetVal    x!38 :: () = ... in ...
    │                                     ├─KNVar(Local):   b!39 :: ()
    │                                     └─KNLetVal    x!33 :: () = ... in ...
    │                                       ├─KNVar(Local):   n!40 :: ()
    │                                       └─KNLetVal    x!42 :: () = ... in ...
    │                                         ├─KNVar(Local):   b!43 :: ()
    │                                         └─KNLetVal    x!41 :: () = ... in ...
    │                                           ├─KNVar(Local):   n!44 :: ()
    │                                           └─KNLetVal    x!45 :: () = ... in ...
    │                                             ├─KNVar(Local):   b!46 :: ()
    │                                             └─KNLetVal    x!32 :: () = ... in ...
    │                                               ├─KNVar(Local):   n!47 :: ()
    │                                               └─KNLetVal    x!50 :: () = ... in ...
    │                                                 ├─KNVar(Local):   b!51 :: ()
    │                                                 └─KNLetVal    x!49 :: () = ... in ...
    │                                                   ├─KNVar(Local):   n!52 :: ()
    │                                                   └─KNLetVal    x!53 :: () = ... in ...
    │                                                     ├─KNVar(Local):   b!54 :: ()
    │                                                     └─KNLetVal    x!48 :: () = ... in ...
    │                                                       ├─KNVar(Local):   n!55 :: ()
    │                                                       └─KNLetVal    x!57 :: () = ... in ...
    │                                                         ├─KNVar(Local):   b!58 :: ()
    │                                                         └─KNLetVal    x!56 :: () = ... in ...
    │                                                           ├─KNVar(Local):   n!59 :: ()
    │                                                           └─KNLetVal    x!60 :: () = ... in ...
    │                                                             ├─KNVar(Local):   b!61 :: ()
    │                                                             └─KNVar(Local):   n!62 :: ()


Pass Ordering Constraints: Monomorphization
-------------------------------------------

Once upon a time, we monomorphized closure-converted procedures,
directly before codegenning, and did not bother alpha-converting
duplicated definitions. This turned out to be a bad choice
for a number of reasons:
  * Monomorphization was complicated by the need to manually restore
    proper scope for type subsitututions which had been destroyed when
    closure conversion lifted all closed procedures to a flat top-level.
  * Related to the above point, because we didn't drop unreachable monomorphic
    definitions but did drop un-instantiated polymorphic definitions,
    monomorphization needed to know the original top-level procedures
    to ensure that polymorphic definitions only referenced from unreachable
    monomorphic functions wouldn't disappear.
  * Partly because we didn't do any alpha-conversion or variable substitution
    after K-normalization, a monomorphized program was somewhat second-class,
    and we wound up leaning on the LLVM backend to cover our sins, so to speak.
  * Related to the above point, GC root slots remained purely a backend concern.
    In turn, because LLVM doesn't provide a reusable liveness pass, this meant
    that use of GC root slots and reloads thereof remained unoptimized.
    Profiling of inital microbenchmarks revealed that GC root slot overhead
    was a limiting performance factor in some cases.

We have since moved monomorphization to happen
between K-normalization and CPS conversion & optimization.

Monomorphization shares implementations for types with similarly-kinded
parameters and inserts bitcasts to recover the appropriate type for each
type instantiation. For example, both id:[()] and id:[(Int32, Int32)] will
have the same implementation, which is a procedure of type i999* => i999*.

If monomorphization is performed after closure conversion,
CFG-building is complicated somewhat by the need to deal with
considerations of polymorphism. Also, for example, procedures will be
temporarily polymorphic (before mono), but always monomorphic when codegenned.
Finally, maintaining proper scoping for type
substitutions is trickier when operating on pre-lifted procedures; one
must be careful to propagate the substitution from the definition site
when converting a procedure.

If monomorphization is performed before closure conversion, the
bitcasts inserted for local functions will have function type; if the
associated function might be lifted to a procedure rather than closure
converted, the bitcasts must be modified accordingly. However, this
is no harder updating the call sites from closure applications to
procedure applications.


Neutral facets
~~~~~~~~~~~~~~

We cannot generate GC root slots until after monomorphization due to
unboxed polymorphism, because whether or not a given parameter needs
a gcroot depends on how its type parameters are instantiated.
There are a few potential solutions:
  * Monomorphize before closure conversion.
  * Monomorphize after closure conversion, and have the middle-end
    do a separate analysis of monomorphic and polymorphic core.
  * Monomorphize after closure conversion, and leave stack slot
    generation to the backend. Easy but inefficient: gcroots are
    worth optimizing!

The duplication involved in monomorphization requires consistent
alpha-renaming, which also affects closed-over variables. This is
true regardless of when monomorphization is performed, but doing
it earlier makes it harder to cheat---which argues in favor of doing
it earlier!


Pass Ordering Constraints: may-GC analysis
------------------------------------------

Strict requirement: may-gc information must be computed
before GC root insertion can occur.

Closure conversion loses the call graph
structure that would make it easy to do a bottom-up may-gc
analysis, which suggests doing may-gc computation before closure conversion.

However, closure conversion also makes representation decisions which can
eliminate potential allocations. As a result, if we do may-gc computation
before closure conversion, we'll be forced into a (well, an even more)
conservative estimate of which functions might wind up GCing.

Thus we split the collection into two phases: first, we collect constraints
before doing closure conversion. The primary benefit of this choice is that
we can generate a more efficient constraint set. If ``f`` calls ``h``, and
we know that ``h`` has a known gc effect, we can avoid generating and then
later solving an indirect constraint. After collecting a minimal constraint
set, we wait until after closure conversion to resolve the constraints.

Extending The Language
----------------------

Currently, language extensions require the following modifications:

1. Edit grammar/foster.g with new syntax rules.
2. Edit compiler/parse/ANTLRtoFosterAST.cpp and
     (probably) compiler/include/foster/parse/FosterAST.h
3. Protocol buffer handing:
  * compiler/parse/FosterAST.proto
  * compiler/passes/DumpToProtobuf.cpp
4. Middle-end, to whatever degree is needed.
5. Back-end, maybe: compiler/fosterlower.cpp

Compiler Details
================

.. toctree::

        closureconversion
        fosterlower
        compiled-examples
        coro
        gc
        optimizations
        match-compilation
        recursive-bindings

.. include:: closureconversion.rst
.. include:: fosterlower.rst
.. include:: compiled-examples.rst
.. include:: coro.rst
.. include:: gc.rst
.. include:: optimizations.rst
.. include:: match-compilation.rst
.. include:: recursive-bindings.rst

Stack Allocation
----------------

From an IR perspective, allocating on the stack instead of the heap (mostly)
just involves toggling a flag on an AllocationSource. There's one extra
subtlety: there must also be a GC root pointing to the stack allocation,
and the GC must know to update the stack slot contents without also trying to
copy the slot contents to the newspace.

There are a few choices in how to expose this functionality at the source level
in a safe way. One approach would be to mimic ALGOL, with implicit mutability::

       let x = stackVAR 2; in
         print_i32 x;
         x := 3;
         print_i32 x;
       end

with a typing rule::

                e :: t
       ---------------
       stackVAR e :: t

To support this illusion, expressions of the form ``x := e`` become stores, and
every other use of a stackvar-bound variable is implicitly replaced (after
typechecking) with a load from the backing slot.

The problem with this approach is that a closure ``{ x }`` should not be
rewritten to ``{ load x }``, as there's no check that the closure is only used
when ``x`` is still live. We can account for this with an ad-hoc check, but
that's both ugly and restrictive.

A subtler problem is a poor interaction with lambda-lifting, which removes
variables from a closure's environment if the variable can be provided from
every call site of the closure. Lambda-lifting must become more complicated to
deal with the fact that the value of ``x`` can vary across program points,
unlike all other (immutable) bindings.

A simple alternative would be to leverage the type system a bit::

       let x = stackREF 2; in
         print_i32 (prim stackref-load x);
         prim stackref-assign x 3;
         print_i32 (prim stackref-load x);
       end

with a typing rule::

                e :: t
       ------------------------
       stackREF e :: StackRef t

Now the type system can be given clear rules to enforce safety for
stack-allocated references. Unfortunately, there are two costs:
  #. Majorly, the restrictions for safety prevent *any* function from closing
     over a stackref. As a result, it becomes impossible for a function
     implementing a nested loop to close over a stackref from the outer loop.
  #. Minorly, we need separate primitives for loads from stackrefs vs heaprefs,
     because they involve separate types, and we wouldn't know which type
     to infer for a metavariable.

Here's an example of real code which would run afoul of the major restriction::

        energy = { bodies : Array Planet =>
          let e = (ref 0.0); in
            arrayEnum bodies { b1 : Planet => i : Int64 =>
              incrByFloat64 e ...;
              arrayEnumFrom bodies (incr64 i) { b2: Planet => jj : Int64 =>
                let dx = ...;
                    dy = ...;
                    dz = ...;
                    distance = ...;
                in
                  decrByFloat64 e ...;
                end
              };
            };
            e^
          end
        };

To turn ``e`` into a stackref, we would need to statically know that it's safe
for the ``arrayEnum`` thunk to close over ``e``, which implies knowing something
about the behavior of ``arrayEnum``.

For reference, here are the definitions from the stdlib::

        arrayEnumFrom = { forall t:Type,
                          a : Array t =>
                          k : Int64 =>
                          f : { t => Int64 => () } =>
          if k <Int64 prim_arrayLength a
            then f a[primitive_trunc_i64_i32 k] k;
                 arrayEnumFrom a (incr64 k) f
            else ()
          end
        };

        arrayEnum = { forall t:Type,
                      a : Array t =>
                      f : { t => Int64 => () } =>
          arrayEnumFrom a (primitive_sext_i64_i32 0) f
        };

and the result of inlining these definitions (not currently performed)::

        energy = { bodies : Array Planet =>
          let e = (ref 0.0); in
            rec arrayEnumFromF = { forall t:Type,   af : Array t =>
                                                    kf : Int64 =>
                                                    ff : { t => Int64 => () } =>
                            if kf <Int64 prim_arrayLength af
                              then ff af[primitive_trunc_i64_i32 kf] kf;
                                   arrayEnumFromF af (incr64 kf) ff
                              else ()
                            end
                          };
             rec arrayEnumFromH = { forall t:Type,  ah : Array t =>
                                                    kh : Int64 =>
                                                    fh : { t => Int64 => () } =>
                            if kh <Int64 prim_arrayLength ah
                              then fh ah[primitive_trunc_i64_i32 kh] kh;
                                   arrayEnumFromH ah (incr64 kh) fh
                              else ()
                            end
                          }; in
            in
            let f = { b1 : Planet => i : Int64 =>
                        incrByFloat64 e ...;
                        let h = { b2: Planet => jj : Int64 =>
                                  let dx = ...; // using b1 and b2
                                      dy = ...;
                                      dz = ...;
                                      distance = ...;
                                  in
                                    decrByFloat64 e ...;
                                  end
                                }; in
                          arrayEnumFromH bodies (incr64 i) h;
                        end
                      };
            in
              arrayEnumFromF bodies (primitive_sext_i64_i32 0) f
              e^
            end
          end
        };

Now that ``arrayEnumFrom`` has been inlined, each instantiation gets passed
a single return continuation (trivially, because they each have a single
external call site and the only internal calls are tail calls). As a result,
the instantiations are both eligible for contification. Another benefit of
inlining is that ``fh`` and ``ff`` both have only one thunk which can flow
to the respective binder. As a result, inlining ``f`` for ``ff`` is a shrinking
reduction::

        energy = { bodies : Array Planet =>
          let  e = (ref 0.0);
          cont arrayEnumFromH = { forall t:Type,  ah : Array t =>
                                                  kh : Int64 =>
                                                  fh : { t => Int64 => () } =>
                          if kh <Int64 prim_arrayLength ah
                            then fh ah[primitive_trunc_i64_i32 kh] kh;
                                 arrayEnumFromH ah (incr64 kh) fh
                            else ()
                          end
                        }; in
          cont arrayEnumFromF = { forall t:Type,   af : Array t =>
                                                  kf : Int64 =>
                          if kf <Int64 prim_arrayLength af
                            then
                              let b1 = af[primitive_trunc_i64_i32 kf];
                                  i  = kf;
                              in
                                incrByFloat64 e ...;
                                let h = { b2: Planet => jj : Int64 =>
                                          let dx = ...; // using b1 and b2
                                              dy = ...;
                                              dz = ...;
                                              distance = ...;
                                          in
                                            decrByFloat64 e ...;
                                          end
                                        }; in
                                  arrayEnumFromH bodies (incr64 i) h;
                                end
                              end;
                              arrayEnumFromF af (incr64 kf)
                            else ()
                          end
                        };
          in
              arrayEnumFromF bodies (primitive_sext_i64_i32 0)
              e^
          end
        };

As it happens, inlining ``h`` is also safe, but in general, safely doing such
inlining requires a proof that the environment of ``h`` at its definition site
is the same as at its call sites. In the general case, given an oracle answering
queries about which functions flow to which call sites, inlining requires
environment analysis (a.k.a. must-alias analysis), as pioneered by Matt Might
and Olin Shivers. However (and fortunately for us!) I believe that data flow
analysis by itself cannot identify flows-to facts which would be unsound without
environment analysis.

Inlining ``h`` yields::

        energy = { bodies : Array Planet =>
          let  e = (ref 0.0);
          cont arrayEnumFromH = { forall t:Type,  ah : Array t =>
                                                  kh : Int64 =>
               if kh <Int64 prim_arrayLength ah
                 then
                   let b2: Planet = ah[primitive_trunc_i64_i32 kh];
                       jj : Int64 = kh;
                   in
                           let dx = ...; // using b1 and b2
                               dy = ...;
                               dz = ...;
                               distance = ...;
                           in
                             decrByFloat64 e ...;
                           end
                   end;
                   arrayEnumFromH ah (incr64 kh) fh
                 else ()
               end
             }; in
          cont arrayEnumFromF = { forall t:Type,   af : Array t =>
                                                   kf : Int64 =>
                if kf <Int64 prim_arrayLength af
                  then
                    let b1 = af[primitive_trunc_i64_i32 kf];
                        i  = kf;
                    in
                      incrByFloat64 e ...;
                      arrayEnumFromH bodies (incr64 i);
                    end;
                    arrayEnumFromF af (incr64 kf)
                  else ()
                end
              };
          in
              arrayEnumFromF bodies (primitive_sext_i64_i32 0)
              e^
          end
        };

Inlining has implicitly eliminated closure allocation and turned the code
into an efficient pair of nested loops, exactly as would be generated by
a primitive looping construct.


Delta-CFA
~~~~~~~~~

http://matt.might.net/papers/might2006dcfa.pdf gives this example of a
hard-to-spot inlining opportunity::

        (\_z (z)
          (letrec ((loop (\_lp (f s)
                 [f s (\_fs (fs) (loop f fs))])))
            (loop (\_o (x k) (k z)) 0)))

rewritten::

        { z =>
          let cz = { x => z };
          rec loop = { f s => loop f (f s) };
          in
            loop cz 0
          end
        }

Simple beta-reduction can't spot this, but it's trivial to recognize
in a data-flow framework like Hoopl.

Another (pathological) example::

       let f = { x h => if x == 0 then h ! else { x } end };
       in f 0 (f 3 0) end

As written, that doesn't satisfy a static type checker. However, we can tweak
the example::

       let f = { x m =>
        case m of
          Nothing => Just { x }
          Just h => h !
        end
       }; in f 0 (f 3 Nothing) end

The code as written evaluates to 3. Now, the only lambda which flows to ``h``
is ``{ x }``, so we might go ahead and inline (and beta-reduce) it::

       let f = { x m =>
        case m of
          Nothing => Just { x }
          Just h => x
        end
       }; in f 0 (f 3 Nothing) end

This is wrong: the result is now 0 instead of 3.  One way of seeing why this
inlining was bogus is that ``{ x }`` escaped from the scope of the binding of
one of its free variables, which introduced the opportunity for it to go wrong.
Consider this very similar example::

       let x = ...;
           f = { z m =>
        case m of
          Nothing => Just { x }
          Just h => h !
        end
       }; in f 0 (f 3 Nothing) end

Now the inlining is a-OK; the difference is that ``{ x }`` never escapes the
scope of ``x``. This view is **more conservative** than delta-CFA: if the
original example ended with ``f 3 (f 3 Nothing)``, delta-CFA would observe that
the inlining were acceptable, because the environments are guaranteed to be
equivalent (up to free variables) at the definition and use points of the
closure. On the other hand, the scope-escaping view would conservatively reject
the possibility of inlining, because the closure **escapes** the scope of ``x``.

.. note::

   In a data-flow framework, "escaping" is even more conservative, and I don't
   think that the environment problem actually occurs in practice without using
   aggressive control-flow analysis, which can reason about where returned/
   escaping values can flow. Consider: in order for a function to escape the
   scope of one of its free variables, the function must escape upwards, but
   return continuations are completely opaque to pure data flow analysis...

.. note::

   Research question: how common is it to encounter call sites with one known
   callee, where the callee may escape the scope of its innermost free variable?


