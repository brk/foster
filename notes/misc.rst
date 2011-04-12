* Stack-allocated structures are no faster to access than heap-allocated structures,
  at least given a decent calling convention where args are passed in registers.
  Given a function that takes ``S* a`` and allocates a local ``S b``, a read from
  ``a->c`` compiles to ``4(%rbx)``, while a read from ``b.c`` compiles to
  ``-16(%rbp)``.
