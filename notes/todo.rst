TODO
====

* Measure impact of alignment (1 vs 4)? vs 8 vs 16 --
  can enable SSE2+ insns for align 16, but can also raise memory usage.
* Can begin doing comparative timing tests for verifying efficient
  implementation of high level idioms.
* Document motivation for reasoning about mapping of first-class
  functions to (environment-less) first-order procedures:
    * performance
    * FFI interop
  and measure performance overhead of closure-call vs proc-call.
* Write up measurements in paper form for jms/stevez/milo/etc.
* Measure the impact of adding pointer analysis to a type-safe language
* Measure impact of "low level" vs "high level" optimizations
* Determine what tradeoffs exist between safety & "pay as you go"
* Think about competing philosophies: "this code should be safe from all mischief"
                                  vs  "the language shouldn't get in my way or
                                       prevent me from doing what i need to do"

Instrument CFG generation to track metrics:
* # of distinct program points
* # of distinct scopes
* # of basic blocks
* # of functions
* distribution of #/size of basic blocks over functions

Far future: GHC plugin to dump strict Haskell to Foster?
        https://github.com/thoughtpolice/strict-ghc-plugin/blob/master/Strict/Pass.lhs

Far future: Translation of Ironclad C++ into Foster?

Describe similarities/differences of CFG/SSA/CPS
        Minor delta in Hoopl representation! Call becomes a terminator.

Optimization idea: given IL -> Src transform,
               compile    === compile | uncompile | compile
               Src -> IL  === Src -> IL -> Src -> IL
  (restricted case of IL  ===        IL -> Src -> IL)

  Something like "the target code idioms generated should be directly
                  representatable with source langauge constructs."

General Compiler Structure Improvements
---------------------------------------
* Move pattern match compilation earlier in the pipeline?
        * Requires "hand-compiling" pattern matches on env tuples.
* More regular IL constructs for recursive values and/or closures.
* Use newtypes to distinguish old-vs-new cases when doing
  transformations from an IR to an implicit subset.

* Better phi handling:
  * Args to postalloca phi use emit()
  * Args to internal (non-postalloca) phis use codegen()

* Have ctest -V's invocation of run_all.py pass -I ../stdlib by default.

TODO: libraries, benchmarks, & applications
-------------------------------------------
* Well-known collection types to runtime (lists, etc)
* Local vars?
* Strings - partially done
* Hash tables
* Sequences
* Persistent maps
* MP integers
* C interop story
  * GC design
* 32-bit floats
* Flonum vectors
* Fixnum vectors
* Growable vectors
* Parallel benchmarks?
* Timing infrastructure

TODO: mutability & representation semantics
-------------------------------------------

1) Design IR, document tradeoffs (such as: unboxed updates only on single-ctor
                                           data types)
2) Implement IR primitives & typechecking.
2) Implement unboxing (and arity raising, etc) optimizations.

TODO: minor optimizations
-------------------------
* Ensure that code like ``case foo of (bar, baz) -> (bar, baz) end``
  doesn't do any heap allocation (when we're returning an immutable value
  identical to (some subterm of) the inspected value).
* Make sure linear chains of variable remappings don't trigger O(n^2) behavior.
        should be fixed now, but should still test just in case
* Eliminating redundant stack slots for phi nodes?
* Arity raising/unit elimination
* Worker/wrapper for closures??
* Track integer ranges and omit bitshift masks when possible.

* Work to minimize generated protobuf sizes.
  Empirically, bytes are spent most heavily for 23 (call), 24(seq), 19(let),
                                                14 (var), 30 (case_expr),
    Removing 502 single-element SEQ nodes saved 10845 byes, ~21 bytes per SEQ.
    Removing one optional field from Expr saved 1509 bytes.
    Omitting source ranges saved 34% (39kb).
                                                                       
* reuse stack slots
  for code like ``(letstack s0 = ... in ... end, letstack s1 = ... in ... end)``

TODO loop optimizations
-----------------------

* Make sure that hof-while gets compiled to good code (inlining?)
* Recognize loops and loop nesting levels
* Perform more aggressive specialization inside nested loops.

* When making a function call in a loop (any loop, tail-rec vs until
  doesn't matter), LLVM is performing unnecessary copies to make sure that the
  callee isn't mucking up stack slots that should be preserved across calls.
    * First: does this actually lead to measurable overhead? Per million iters?
    * Removing three reg-to-mem copies in a tight loop (1e9 iters)
      saves 420 ms (= 3.38 - 2.96).
      Extrapolating, 1e6 iters would save 0.42 ms,
      and the cost per 1000 iters is 420 ns.

* Move stack stores for invariant function args from postalloca to entry
  (minor efficiency gain for tail-recursive functions).
  Basically the exact same cost analysis as above.

TODO: less minor optimizations
------------------------------
* Generate unknown/polymorphic wrappers on-demand:
  ``f_unknown(env, args) = case args of (x,y,...,z) -> f_known(env, x,y,...,z)``
* Think about function arity, type inference, higher rank functions...

* LLVM register maps/liveness info for GC
* Flow-sensitive type systems -- emission of proof witness values?
* Simple effect analysis, effect-based optimizations?
        Memoization a la Tarditi's dissertation

TODO: implementation details
----------------------------
* rusage() in runtime when on Linux (+ OS X?)

* Interaction between primitive integer types and polymorphism at LLVM level.

* Expand use of chromium-base
 * Use format_macros.h
 * stringprintf.h ?
 * Keep statistics of GC/mutator run times?
  * metrics/stats_counter.h
  * metrics/histogram.h
  * perftimer.h (would need modification)
* Benchmarking/profiling infrastructure
* Implement debug info using DIBuilder.
* Coroutines (mostly done?)
  * On-demand stack growth/detection of impending overflow
  * make foster_coro struct be generic in arg type
  * tracing stack roots up the coro invocation chain
  * Generally: do more testing of GC and coroutines!

TODO: design & implementation
-----------------------------
* Module system.

* Design pointer representations and GC integration:
 * Stable pointers
  * Malloced/foreign memory
  * Pointers to stack-allocated objects
  * Interior pointers (for heap objects)
  * Scheme to control whether a pointer is considered a GC root
  * Invariants for what kinds of pointers can point
    to which other kinds of pointers, and whether pointer kinds are known
    statically or dynamically.
 * Constructor tags on pointers, pointer masking, switching on ctag bits.
 * Escape analysis to enable stack allocation
  * Aligned allocas

* Type operators (types indexed by types)
  * Or type-level turing complete computation?
* Pattern matching (basics done, fancier variants possible:)
  * Arbitrary-sized bintegers
  * Views?

* Algebraic data types (data/variant/oneof)
  * Representation guarantees for restricted cases
    * all zero-arity    => int tags (32 bit?)
    * 1 non-zero arity,
      1     zero arity  => (nullable) pointer to { fields ... }
    * else              => (non-null) pointer to { ctortag, fields... }
    * Interaction with mutability: if cell containing variant A can be
      mutated to variant B, can't store tag bits in pointers.
     
  * Layout situations for data types:
    * Most common: don't care about offsets, access fields indirectly.
    * Sometimes: want interop with C struct layout.
      Field order matters, but struct not packed.
    * Rarely: need bit-level layout (and pattern matching); packed struct.

* Primitive types
  * Integer vs Int32 ?
    * Determining types of literals
    * Overloading of operators like +
      * Abstrcting over one type   : simply-typed functions
      * Abstracting over all types : polymorphic  functions
      * Abstracting over a set of
         types with a common property : type classes?
                                        existentials?
                                        interfaces?
                                        higher-order polymorphism?
                                        higher kinds?
                                        refinements?
                                        dependent types?
          algebraic or other non-structural properties?

  * Arrays
    * Type constructors (dependent types)
    * Card marking?
    * When can an array be unboxed?
  * Records
    * "Struct" vs "hashtable" (open vs closed world)
  * Strings (standard but not primitive, given arrays?)
  * References (done?)
    * Separate from Addr? Fat ptr for interior refs?

* Mutability
 * Effects, a la Disciple
 * Arrays
 * Local variables mutable? Need explicit ref cells?
 * Records
 * Choices:
  * ML-style explicit refs
  * C/Go explicit pointers
  * Java implicit pointers
  * Disciple implicit refs

* Impredicative polymorphism, notes from
  http://www.eecs.harvard.edu/~greg/cs256sp2005/lec15.txt
 * Monomorphization (aka polyinstantiation), as in C++ and ML:
  * Lose separate compilation, though pre-generating commonly used versions
    probably makes this a non-issue wrt compilation performance.
  * Lose the ability to pass polymorphic functions as first-class values.
 * Uniform representation: simple, slow, makes monomorphic code "pay" for
   polymorphic code.
 * Coersions, intensional type analysis: subtle...
 * Idea: (need to review whether this actually works...)
  * The potential cases for polymorphic function definitions
   can be classified as follows:
    * Top-level function, used internally (not exported)
     * Use natural representation types for function parameters;
       each call site "registers" a signature they need generated.
    * Top-level function, exported
     * Pre-generate boxed version, but also include source
       for others to generate specialized (monomorphic) versions as needed.
    * Function literal not at top level
     * Presumably will eventually be used as a function argument, so...
    * Function argument of function type
     * Assume all args are boxed.
  * This means that the identity function defined at top level
    will result in specialized id_i32 and id_ptr and id_float etc,
    whereas a function argument of type (All a. a -> a) will be represented
    with a function of type (voidPtr -> voidPtr), along with accompanying
    box/unbox coercions for any applied arguments of non-reference type.


* Naming and modules
  * Need to decide how and where to do globalization and resolution.
   * Before emitting protobuf from fe?
   * Before doing typechecking in me?
  * When/where do we convert from unqualified names to fully-qualified names?
  * Is a fully-qualified name just a module name + identifier?

* Interfacing with C libraries:

Benchmarks
==========

nbody
-----

* determine why we're executing so many extra insns

fannkuch?
---------




