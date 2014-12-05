Miscellanous Tidbits of Knowledge
=================================

* Stack-allocated structures are no faster to access than heap-allocated structures,
  at least given a decent calling convention where args are passed in registers.
  Given a function that takes ``S* a`` and allocates a local ``S b``, a read from
  ``a->c`` compiles to ``4(%rbx)``, while a read from ``b.c`` compiles to
  ``-16(%rbp)``.

* If a Foster program silently fails, check ``gclog.txt``.
* If the return value is 99, it means the GC detected an error while running.
* The GC heap size can be configured with ``--foster-runtime '{"gc_semispace_size_kb":400}'``
* Semispace memory is initialized to 0x66, so a SIGSEGV crash with an address of
  mostly 6's means a read of uninitialized memory.
* When semispace memory is cleared, it is changed to 0xFE.
* To see where allocations are coming from, compile with
  ``--be-arg=-gc-track-alloc-sites``.
  This will cause the compiler to emit calls to ``record_memalloc_cell`` before
  each allocation, which will in turn cause dump_stats() to emit extra information
  about call site distribution. By default, dump_stats() goes to ``gclog.txt``.
* Inlining is disabled by default, even with ``--optimize=O2`` (because
  ``--optimize`` is for the backend (LLVM), not the middle end (Haskell).
  Use ``--me-arg=--inline`` to enable it.
* To see monomorphized, inlined, and loop-headered variants of the input program,
  use ``--me-arg=--dump-ir=mono``.

* To convert a UTF-8 encoded string (say, as copied from a web page) into the
  corresponding byte sequence expressed as a Foster machine literal array,
  use a snippet of Python code in http://repl.it/languages/Python/ like so::
      def arra(s):
        print "prim mach-array-literal " + ' '.join(str(ord(x)) for x in list(s))
  and its length via ``len(s.decode('utf-8'))``.
* Can't yet mix ``|>`` sugar with primitive applications.
* Case analysis on literal tuples will not result in runtime allocation,
  so long as the value of the tuple is never captured.
  This capacity subsumes built-in control flow operators like ``&&`` and ``||`` in C.
* Shift amounts are silently masked to avoid undefined behavior.
* Arithmetic operations (``+``, ``-``, ``*``) come in several variants:
  * Regular, which has 2s-complement overflow semantics,
    and thus does not distinguish between signed & unsigned bit patterns.
  * Checked, in signed/unsigned variants, which immediately terminates the program
    if/when an overflow occurs.
  * The checked variants may be used explicitly (such as ``+ucInt32`` and ``-scWord``),
    or the prelude file ``primitives-checked`` may be included to rebind the default bindings.
  * TODO: use an SMT solver to identify when a checked variant could be
          optimized to a raw operation, and vice versa.
* Inline asm syntax::

    prim inline-asm :[ { () } ]
                    "cli ; sti"
                    ""
                    True;

  The required arguments are: an overall function type for the assembly code,
  the text of the code itself, the text of the constraints on the assembly code,
  a boolean indicting whether the assembly code has effects, and zero or more
  arguments corresponding to the assembly code's "function parameters".
* Calls in the LLVM IR can be marked as non-allocating in one of several ways:
   * ``LLCall::codegen`` will mark calls as non-allocating, or insert a
     pseudo-comment saying that the call may GC. These comments are stripped by
     LLVM optimization, so they only appear in ``out.raw.ll``.
     The may-gc information is derived from ``canGC`` in ``ILExpr.hs`` using
     extra information from
     ``(collectMayGCConstraints + resolveMayGC)``,
     and threaded through ``ILLetVal``.
     Pass ``--me-arg=--dump-ir=maygc`` to view the intermediate MayGC constraints.
   * Our ``GCMallocFinder`` plugin will mark calls as non-allocating. The plugin
     is called as a cleanup pass. By default, ``fosterlower`` runs the pass
     between the ``raw`` and ``prelinked`` stages. ``fosteroptc`` will only run
     the pass if passed the ``-cleanup-only`` flag. Pass ``--be-arg=-dump-stats``
     to see how many calls were marked by the LLVM plugin via ``fosterlower``.
     Note that stats are dumped to a text file in the compilation target dir,
     not stdout.
* Newtype-style wrappers are supported: given a type definition like
  ``type case TU : Type of $D Int32;``, calls to ``D`` will not allocate at
  runtime (should erase completely before LLVM IR emission, actually).
  Also, boxed newtype-style definitions like
  ``type case TX of $FX TB;`` will have calls to ``FX`` translated into simple
  bitcasts.

* Gotcha:
  Functions referenced in refinements must have top-level type annotations.

