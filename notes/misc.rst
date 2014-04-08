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
