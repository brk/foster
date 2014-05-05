* Stack-allocated structures are no faster to access than heap-allocated structures,
  at least given a decent calling convention where args are passed in registers.
  Given a function that takes ``S* a`` and allocates a local ``S b``, a read from
  ``a->c`` compiles to ``4(%rbx)``, while a read from ``b.c`` compiles to
  ``-16(%rbp)``.

* If a Foster program silently fails, check ``gclog.txt``.
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
