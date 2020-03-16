Miscellanous Tidbits of Knowledge
=================================

* Stack-allocated structures are no faster to access than heap-allocated structures,
  at least given a decent calling convention where args are passed in registers.
  Given a function that takes ``S* a`` and allocates a local ``S b``, a read from
  ``a->c`` compiles to ``4(%rbx)``, while a read from ``b.c`` compiles to
  ``-16(%rbp)``.

* If a Foster program silently fails, check ``gclog.txt``.
* If the return value is 99, it means the GC detected an error while running.
  If the return value is 255, it means the GC ran out of heap space.
* The GC heap size can be configured with ``--foster-heap-MB 400``
* To unsafely disable array bounds checking (e.g. to see how much speedup is
  possible, without going to the trouble of establishing the necessary invariants)
  use ``--be-arg=-unsafe-disable-array-bounds-checks``
* To see where allocations are coming from, compile with
  ``--be-arg=-gc-track-alloc-sites``.
  This will cause the compiler to emit calls to ``record_memalloc_cell`` before
  each allocation, which will in turn cause dump_stats() to emit extra information
  about call site distribution. By default, dump_stats() goes to ``gclog.txt``.
* Inlining is disabled by default (as its name suggests, ``--backend-optimize``
  is for the backend (LLVM), not the middle end (Haskell).
  Use ``--me-arg=--inline`` to enable it.
* To see monomorphized, inlined, and loop-headered variants of the input program,
  use ``--me-arg=--dump-ir=mono``.
* Most allocations, (but currently not arrays) are zero-initialized on allocation.
  A flag is threaded through from ``AllocInfo`` through to ``LLCodegen.cpp``.
  For arrays, ``ProtobufIL.hs`` directly sets the flag when dumping arrays.

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
  
* Newtype-style wrappers are supported: given a type definition like
  ``type case TU : Type of $D Int32;``, calls to ``D`` will not allocate at
  runtime (should erase completely before LLVM IR emission, actually).
  Also, boxed newtype-style definitions like
  ``type case TX of $FX TB;`` will have calls to ``FX`` translated into simple
  bitcasts.

* For now, such wrappers cannot be generalized to unboxed structs.
  There are several reasons for this -- no fundamental impediments, just
  annoyingly unclear design decisions to settle:
    * In LLVM's abstract semantics, values in SSA registers cannot be moved
      by a GC. So an unboxed tuple must either not contain any GCable pointers,
      or the tuple must be stored in memory.
    * If the tuple is to be stored in memory: when should it be copied to/from
      memory? Should an unboxed-struct function parameter be a SSA value which
      is stored in every stack frame it is threaded through, or represented as
      a pointer to a higher stack slot? (If it was pointing to a heap slot, it
      would be a regular tuple, not a struct). If representing with a pointer,
      we must be careful not to create dangling references when storing such a
      struct into a heap cell. But not representing with a pointer brings its
      own troubles; in particular, GC root slots must contain only pointers,
      not arbitrary struct types.
      Also, if we store structs on the stack, we must be rather careful to
      align things properly for GC'ing -- in particular, the *payload* must be
      16-byte aligned, which in turn means that we need 16 bytes of padding...


* Gotcha:
  Functions referenced in refinements must have top-level type annotations.

Profiling
---------

Every run of ``me`` will produce ``meGCStats.txt``, which says how many bytes
were allocated and the relative time spent in mutator/GC/etc.

Use ``--profileme`` to also enable various forms of profiling.
By default, ``run_test.py`` passes ``-p`` for a time profile, and
``-hc`` for a by-function space profile. Results go in ``me.prof`` and ``me.hp``
respectively.

``me.prof`` is a text file that can be viewed in ``vim`` etc. However, it
contains many extraneous lines; run ``filter-me-prof me.prof`` to generate
``me.prof.txt``.

Run ``hp2ps -e8in -g -c me.hp && gv me.ps`` to view the profile via a generated
``me.ps`` file.

GHC 8.2 learned to output profiles in JSON format.
There is a tool called ``ghc-prof-aeson-flamegraph``, installable via ``cabal``,
which can turn such profiles into flamegraphs. Example::

    gotest.sh test-bigint --profilemejson
    cat me.prof | ~/foster/compiler/me/.cabal-sandbox/bin/ghc-prof-aeson-flamegraph | ~/FlameGraph/flamegraph.pl > me.svg
    firefox me.svg

.. note:
        See also https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/hp2ps.html


Native Code Interop Example: SDL2
---------------------------------

A command line to build a C++ program against SDL2 might look something like this::

    clang++ simplegl.cpp -O2 -lm -lSDL2 -lGL -lGLEW -std=c++11 -o simplegl.exe

Foster provides (some) support for linking aginst such libraries as well.
Foster's foreign language support is oriented around functions and primitive types.
Unlike the equivalent C++ program, Foster cannot make direct use of the preprocessor,
nor can Foster access constants or perform direct struct member lookups.
To bridge the gap, you must wrap such functionality in a small auxilliary C library.
For the "hello world" equivalent in SDL, we only need two such helper functions::

    #include <SDL2/SDL.h>

    SDL_PixelFormat* SDL_GetSurfaceFormat(SDL_Surface* s) { return s->format; }
    SDL_Rect* SDL_NullRect() { return NULL; }

These symbols can be imported and used on the Foster side like so::

    foreign type SDLPixelFormat;
    foreign type SDLSurface;
    foreign import SDL_GetSurfaceFormat as sdlGetSurfaceFormat :: { SDLSurface => SDLPixelFormat };

    main = {
       ...
       surface = ...;
       pixfmt = sdlGetSurfaceFormat surface;
       ...
    };

We begin by compiling the above library (in ``sdlWrap.c``) to LLVM bitcode::

    clang sdlWrap.c -emit-llvm -c -o sdlWrap.bc

Putting potential hot-loop operations, such as struct accesses, behind a function call
boundary might seem doomed to be slow. But fear not!
LLVM's powerful optimizer will boil away the wrapper functions when we compile
our program with ``--backend-optimize``.

We can then compile and run our program, linking the SDL library and our wrapper::

    runfoster simplegl.foster --nativelib SDL --bitcode sdlWrap.bc --backend-optimize

We can also compile to a native executable::

    fosterc   simplegl.foster --nativelib SDL --bitcode sdlWrap.bc --backend-optimize -o fostergl.exe

