Compiler History
================

The compiler was originally a monolithic C++ binary.
It is now a separate front-end, middle-end, and back-end,
which communicate via CBOR and Cap'n'Proto buffers.

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
* It's easier to link against our standard library,
  especially when we don't know the types of certain symbols
  in advance.
* In case we revisit using LLVM's GC support:

  * We can use a custom GC plugin.
  * It seems easier to do GC metadata & type maps this way.

LLVM provides some support for loadable modules, which enables
passes to be dynamically loaded into standard LLVM tools like
``opt`` and ``llc``. Unfortunately, that functionality was not
supported on Windows (I haven't checked lately, though!).
That left the option of writing a copy of ``opt`` and/or
``llc`` which statically link in our plugin and passes.
Currently, we have a ``fosterlower`` binary, which converts
Cap'n Proto with a close-to-LLVM representation, and outputs
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
operators correspond in structure to their source ordering, not their
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
  * ``Module`` to asm/obj (may require GC plugin)
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

  The main problem is that the decision tree for the above
  case analysis contains 28 leaf nodes,
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


Pass Ordering Constraints: Pattern Matching
-------------------------------------------

As discussed below, we originally generated decision trees in the middle-end,
and built CFGs from them in the backend. This was mostly because the frontend
did not yet have a notion of CFG to represent the decision trees with. Decision
tree compilation was done along with closure conversion; this permitted closure
conversion to bind variables from the environment via a tuple pattern match.

Later, the middle-end learned to build CFGs on its own.
The play between pattern matching and the CFG was this:

* When converting pattern matches in K-normal-form expressions,
  placeholder CFG block identifiers would be generated for the leaves
  of the decision tree. Each such block would compute the appropriate
  case arm's body expression value and jump to the continuation of the
  pattern match.
* The resulting case expression, with block identifiers substituted for the
  case arm body expressions, was used as a terminator in the CFG.
* Later on, pattern match compilation would build decision trees from nested
  pattern matches.
* These decision trees, in turn, would be compiled to further CFG
  structure, primarily to wrap the placeholder blocks with CFG nodes
  to introduce the bindings scoped over the expression body.

Unfortunately this scheme doesn't extend well to efficient compilation of
guarded pattern matching. The reason is that when generating the initial CFG,
we get stuck on how to handle guarded patterns. Ideally we want to generate
the guard expression, followed by a branch to either the body expression or
a sub-CFG corresponding to the rest of the viable pattern matches from the
current state of the matching automaton. Unfortunately we can't do that, because
it would involve a circular dependency across disjoint compiler stages.
We could hack around it in super gross ways, such as generating a temporarily-invalid
CFG (with a missing "false" block), or by deferring the CFG-ization of the body
expression until we can generate the corresponding false-block logic.

Instead, in the near term, we'll do a simple source-to-source translation
before/at K-normalization to represent guarded pattern matches as linear
chains of matches. This will be inefficient but non-disruptive to the
existing limited infrastructure.

Longer term, we can leverage our investment in contification optimizations
to implement pattern match compilation as a source-to-source translation
from nested to flat matches, as MLton does.

Data Structure Representation
-----------------------------

Given a type like::

    case type T
      of $C1
      of $C2
      of $C3 c3t1 ... c3tn

Every value of type T has boxed kind, and
the baseline representation for ``c1 = C1 ! ; c3 = C3 ... ;`` is::

    c1:[_*]    [tagptr|~~~padding~~~]
         +-------------^

    c3:[_*]    [tagptr|c3t1|...|c3tn]
         +-------------^

All of the constructors are represented as word-sized values pointing to
a tagged heap cell.
The garbage collector uses the tag pointer to determine how to collect
the tagged constructor cell, and pattern matching also uses the tag
to determine what the "small id" of the constructor is.

There are a few representation optimizations that can be made in
specific situations:

* (aka strict newtype) If T has a single constructor with a single field of the same
  boxity as T itself, then C needs no direct runtime representation
  (modulo perhaps maintaining metadata for debugging).

   * This optimization also applies when T has at most one non-nullary ctor, but
     **only** if the wrapped type in turn contains no nullary ctors.

* (aka c-like-struct) If T has a single constructor, it is eligible for unboxed
  representation in certain situations, such as ref update...
* If the GC can handle pointers to static data, the constant constructors could be
  made to point at preallocated values. This saves an allocation and keeps the
  representation simple and uniform.
* If T has several non-nullary constructors, they (up to 8 of them = 3 bits, keeping
  one bit spare for other purposes) can be represented as tagged pointers.
  Tagging pointers implies that pattern matching is faster
  (because it can sometimes avoid cache misses/memory indirection hits)
  at the cost of a few extra ALU operations.
* If T has at most one non-nullary constructor, then the nullary constructors could
  be represented as tagged null pointers (i.e. uint8 zext to intptr_t).
  The non-nullary constructor gets the (effective) tag of zero.
  This brings the cache-benefits of tagged pointers, without the extra ALU operations
  needed to untag pointers before dereferencing them.

.. todo::
     if we use only the low-order bits of each word, then we can only encode
     up to 8 constructors (16 if we use all 4 low bits). We could use a segmented
     representation to encode more constructors at slightly greater ALU cost.
     For example, the most common constructors could be tagged in the low bits,
     so that a simple (& 0b1111) would identify those constructors, while
     (say) a masked value of 0b1111 would indicate that the remaining tag bits
     are in the higher ~28 bits of the word.

.. todo:: is BIBOP actually "inefficient and clumsy" as Appel claims,
     or is it advantageous because, for example, we wind up always
     having the cache line for the descriptor at hand?

For now, we'll implement a baseline optimized representation:
nullary constructors will be represented as tagged (with a nonzero tag)
small integers, plus the strict newtype optimization.

Concretely, the standard representation is a tidy pointer to a tagged heap cell.
Looking up ``x1``'s tag for pattern-matching requires an indirection::

    type T1
      of $C1  a b
      of $C1x a b

    x1 = C1 a b
               {[C1|a|b]}
                   ^
    x1 [*]---------+

Transparent representation is compiled away in the middle-end for constructor
applications.  When looking up occurrence information, the backend will insert
bitcasts to resolve type mismatches (as it does with regular indirections)
but will omit ``getelementptr``::

    type T2
      of $C2 T1

    x2 = C2 x1
               {[C1|a|b]}
                   ^
    x2 [*]---------+

Nullary constructors can be represented more efficiently, such that
no allocations are required and finding tag bits is a simple mask operation::

    type T3
      of $C3
      of $C3x

    x2 = C3 !

    x2 [*] = [000000000000000|tag]

One small complication is that the garbage collector must now recognize
that such values are not actually pointers and should not be deref'ed.
Another complication is that while the typemap info accessible through
the tag pointer is not needed, there is other information -- such as
strings to describe the value's type -- which is useful to have even
if there is no associated physical heap cell. Conceptually that information
should be recoverable through a runtime interface like ``(TypeRep, CtorTag) -> CtorMeta``.

Data constructor representations have the following lifetime:
  * A representation is assigned to constructors in KNExpr.hs
  * This representation is propagated through the syntax tree, decorating patterns in match exprs.
  * During pattern match compilation, we also introduce representations for primitive constructors
    like booleans.
  * A given LLSwitch expression in the backend must know the method it should use to
    find the tag of the scrutinee: raw value (for integers), mask it (for nullary ctors),
    or query the runtime (for untagged objects).


The GC then has a number of cases to consider:
  * Tagged pointer (which may or may not be null when untagged)
  * Pointer to start of heap cell (1 word before a tidy pointer) (``heap_cell*``)
  * Tidy pointer (``tidy*``)
  * Interior/untidy pointer (``intr*``)
  * Untagged pointer
  * Pointer into copying/noncopying/non-/foreign heap space


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

Historical Note: Integer Syntax
-------------------------------

Early prototypes of the language adopted a base-suffix syntax for
integer literals, such as ``101101_2`` to represent 41.
This design was taken from the Fortress language
(via a blog post from Guy Steele that is now lost to the sands of time).
Such literals are (arguably) prettier than the ``0b101101`` style.
One downside of this scheme is that it introduces an
ambiguity: should ``ff_16`` be lexed as a digit or an identifier?
The obvious solution is to require a leading digit (such as ``0``),
but in doing so we're halfway towards the traditional solution of
a leading zero plus a base specifier.
Plus, we end up needing six characters: ``0ff_16`` instead of four: ``0xff``.
And the leading zero looks pretty silly in cases like ``0FFFF`FFFF`0000`0000_16``
Finally, the scheme suggests support for (unsupported) arbitrary bases.

