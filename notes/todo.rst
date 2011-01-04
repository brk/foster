TODO
----

* Arrays
  * Type constructors
  * Card marking?
* Records
* Strings
* References
  * Separate from Addr? Fat ptr?
* Coroutines
  * On-demand stack growth/detection of impending overflow
  * make foster_coro struct be generic in arg type
  * tracing stack roots up the coro invocation chain
* Test that recursive closures work as expected

* Type operators (types indexed by types)

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
* Records: open world vs closed world, Lua tables vs C structs...

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


* chromium-base
 * Use format_macros.h
 * stringprintf.h ?
 * Keep statistics of GC/mutator run times?
  * metrics/stats_counter.h
  * metrics/histogram.h
  * perftimer.h (would need modification)
