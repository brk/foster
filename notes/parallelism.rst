Parallelism
===========


NESL
++++

* Vcode is a thin wrapper around hand-optimized native parallel algos
  in the C Vector Library.
* "Sequences of fixed-size structures (such as pairs) are represented
  as multiple vectors (one for each slot in the structure) that use a
  single segment descriptor."
* GC: segmented free lists + refcounts
* Chatterjee's dissertation of optimizing compiler for NESL to a MIMD
  architecture: "cluster computation into larger loop bodies, reduce
  intermediate storage, and relax synchronization constraints."



Misc
++++

http://www.upcrc.illinois.edu/summer/2009/slides/062509_UPCRC_Research_Snir.pdf

What would make parallel programming easier?

* Isolation: effect of the execution of a module does not depend on other
  concurrently executing modules.
* Concurrency safety: isolation is enforced by the language.
* Determinism: program execution is, by default, deterministic;
  nondeterminism, if needed, is introduced via explicit notation.
* Sequential semantics: sequential operational model, with simple correspondence
  between lexical execution state and dynamic execution state.
* Parallel performance model: work, depth.








































