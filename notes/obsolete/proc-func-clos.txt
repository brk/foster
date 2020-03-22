Procedures, Functions, Lambdas, and Closures
============================================

I was confused for some time about the boundaries between procedures, functions, and closures.

First confusion: a Function in LLVM corresponds to a function in C, which only corresponds
to an *optimized* implementation of a more general notion of (first-class) function/lambda
in functional languages.

In Pascal terminology (iirc) a procedure has no return value, unlike a function.

I don't know offhand what distinguishes procs from lambdas or blocks in Ruby.

Meanwhile, a closure is a possible choice implementation for implementing lambdas.


Terminology inside the Foster compiler is thus:

  * At source level, there are only function values and function types.

  * At LLVM level, there are only procs (``llvm::Function``) and closures.
    A proc is a value with type pointer-to-Function, and a closure could be
    implemented as either type
    ``{ proc, env* }`` or ``{ proc, v1, ..., vn }*``.

  * Top-level function values become procs; other function values may become
    either procs or closures, depending on whether their environments are empty
    and whether they flow to call sites of unknown functions.
    (This interacts with module semantics and how much magic there must be for
     FFI/C compatibility).

  * A proc may be trivially coerced to a closure.
    This is desirable at the source level,
    but the coercion should be explicit by codegen time.

  * Coercing a closure to a proc requires a very restricted form of JIT
    compilation to embed an ``env*`` into an exectuable code sequence, usually
    called a trampoline. Unfortunately this sequence is disallowed on iOS for
    security reasons, so for now we don't expose a coercion from closure to proc.

  * Procs have an operator ``apply_proc`` which takes a value of LLVM type
    pointer-to-Function and some args.

  * Closures have an operator ``apply_clo`` which takes a closure value and some
    args, extracts a function pointer and an environment pointer, and applies
    the env pointer and the args to the function pointer, using apply_proc.

  * Function types may have annotations indicating calling convention
    for the underlying procedure, and whether the associated function
    symbol is to be translated to a proc type instead of a closure type.
