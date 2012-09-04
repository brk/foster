Recursive Bindings
------------------

This paper < http://www.ittc.ku.edu/~andygill/papers/RecBinds.pdf >
suggests a technique (and semantics) for implementing recursive bindings
in a strict language, without introducing laziness in the semantics
or implementation.

The problem with recursive bindings of expressions, compared to the traditional
restriction to non-expansive terms, is that the placeholders needing updates
might be deeply nested in the heap, rather than immediately accessible on the
heap. Syme suggests leveraging lazy evaluation; in a practical sense, this
provides the needed indirection, error-handling/reporting, and back-patching
logic. The downside is that it introduces a layer of indirection for both values
and code (to check whether a lazy value is being re-entered, corresponding to
non-terminating computation arising from a recursive value binding).

The key idea in the paper by Gill et al is to use distinguished invalid pointer
values (for example, those within unmapped pages) to serve as placeholders for
recursive value pointers, and then leverage the garbage collector to traverse
each recursive value and backpatch deeply-nested placeholder pointers. The
advantage of doing so is to avoid adding an unnecessary layer of indirection.

The downside, of course, is that the checks for ill-founded recursion become
implicit and platform specific---SIGSEGV handlers on POSIX, SEH on Windows---
which, not to put too fine a point on it, sucks. In particular, recovering
from SIGSEGV in a way that allows faults to be cleanly isolated is, I'm
pretty sure, tricky-hairy-scary.

http://www.linuxquestions.org/questions/programming-9/sigsegv-handler-segmentation-fauld-handler-277790/

The above suggests that assembly may be required to munge the PC to avoid
re-executing the same faulting instruction.

----------

GHC similarly uses the GC to eliminate indirections in its heap (but, of
course, not the extra code checks to distinguish thunks from "real" values).

----------

Idea: maybe we can get the best of both worlds by using lazy values a la Syme
to build the graph with platform-independent error handling semantics, and then
use the GC to postprocess the resulting graph?

Idea: we can constrain the GC to a particular logical range of addresses to
fix up, avoiding having it traverse the whole heap. The complication is that
GCs can occur during the evaluation of the graph, and there's no straightfoward
way that I know of to establish the correct low-water-mark in the rearranged
heap...

Idea: well, if GC heaps are more first-class, at least at the implementation
      level, then perhaps the thing to do is to allocate the recursive-binding
      computation in a fresh heap, and then copy the results out to the main
      heap once the recursive graph is fully constructed?

TODO: the DELAY rules from the paper?

TODO: understand the benefits of order-independence wrt Syme's work

TODO: measure the overhead of checking a bit
      vs indirecting (unconditionally)
      vs accessing a pointer directly.
