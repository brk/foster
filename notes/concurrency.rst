Concurrency
===========

Foster does not yet have a defined story for concurrency,
mostly because it's not obvious what "the right thing" is.

Concurrency Infrastructure
--------------------------

I've implemented the functionality to insert safepoints and
poll a timeout flag. This sets a foundation for runtime-controlled
concurrency/scheduling (rather than leaving everything to the OS).

This brings several benefits:

* Control over thread scheduling enables determistic replay and debugging
  of concurrent code.
* It sets the stage for heirarchical scheduling, which in turn offers
  the ability to run untrusted pieces of code with time limits, without
  resorting to extra-linguistic means:
   * http://www.cs.utah.edu/~regehr/papers/sosp00_wip/
   * http://www.bford.info/pub/os/inherit-sched.pdf
* One notable, if not obvious, benefit to not relying on OS threads
  is that concurrent garbage collectors often need to synchronize
  with language-level threads. If language-level threads map to OS-level
  threads, you (A) can't really exploit massive concurrency, and (B)
  very quickly see tail effects when trying to synchronize with threads
  that are probably not actively running. (cite Kliot)


Concurrency Designs/Ideas/Concerns
----------------------------------

 * Models:
    * Concurrent ML: technically shared memory but stylistically message passing
    * Concurrent revisions and `isolation types <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/revisions-oopsla2010.pdf>`_
    * Dag-calculus
    * `Reagents <http://www.ccs.neu.edu/home/turon/thesis.pdf>`_ and join patterns
    * STM
    * `Synchronized-by-Default <http://dl.acm.org/citation.cfm?id=3018747>`_ concurrency
 * Language/Type-based approaches:
    * Thread locality: `Loci <http://www.filpizlo.com/papers/wrigstad-ecoop2009-loci.pdf>`_
    * `cap-based aliasing/isolation <https://pdfs.semanticscholar.org/b319/7b8e8828c270627220c3b9e3f410c0d10dff.pdf>`_,
      `refcaps <http://drops.dagstuhl.de/opus/volltexte/2016/6099/pdf/LIPIcs-ECOOP-2016-5.pdf>`_,
      `LaCasa <https://kth.diva-portal.org/smash/get/diva2:1054689/FULLTEXT01.pdf>`_
    * `Scala Actors <https://pdfs.semanticscholar.org/4155/2943a5a8db263211f059b964e3208b8443ff.pdf>`_,
      `Unified Events and Threads <https://www.cis.upenn.edu/~stevez/papers/LZ06b.pdf>`_
      (`diss <http://citeseerx.ist.psu.edu/viewdoc/citations;jsessionid=B73782953A594DB38F1CBEAB3384262B?doi=10.1.1.145.7352>`_)
    * Go, Rust, Erlang, `DPR <https://www.cs.rochester.edu/u/scott/papers/2014_PLDI_DPR.pdf>`_
 * Non-Preemptive Concurrency
    * `A MODEL OF COOPERATIVE THREADS <https://arxiv.org/pdf/1009.2405.pdf>`_
    * Automatic Mutual Exclusion (AME)
    * Transactions with Isolation and Cooperation (TIC)
    * `Cooperative Reasoning for Preemptive Execution <https://slang.soe.ucsc.edu/cormac/papers/ppopp11.pdf>`_
    * `Effects for Cooperable and Serializable Threads <https://pdfs.semanticscholar.org/5035/1c89e715d8b424cfda321a455c7cbd66479e.pdf>`_
    * `Cooperative types for controlling thread interference in Java <http://dept.cs.williams.edu/~freund/papers/15-scp.pdf>`_
    * `Types for Precise Thread Interference <https://www.researchgate.net/profile/Tim_Disney/publication/267700366_Types_for_Precise_Thread_Interference/links/5466dc1b0cf2397f7829e6b7.pdf>`_
    * `Observationally Cooperative Multithreading <https://arxiv.org/pdf/1502.05094.pdf>`_
    * `coop eval 1 <http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.478.4360&rep=rep1&type=pdf>`_,
      `coop eval 2 <http://jaeheon.info/papers/PLATEAU10.pdf>`_
 * Determinism:
    * Deterministic multithreading: DThreads, RFDet, Parrot,
      `DetGal <http://iss.ices.utexas.edu/Publications/Papers/nguyen14.pdf>`_ ...
    * Deterministic parallelism: DPJ, LVars,
      `Grace <http://courses.cs.vt.edu/~cs5204/fall10-kafura-BB/Papers/Threads/Grace-Safe-Multithreading.pdf>`_,
      `DDDP <http://research.ihost.com/tramp/bacon-tramp.pdf>`_,
      `Internally Deterministic Parallel Algorithms Can Be Fast <https://www.cs.cmu.edu/~guyb/papers/BFGS12.pdf>`_,
      `Data-Parallel Finite-State Machines <https://www.microsoft.com/en-us/research/publication/data-parallel-finite-state-machines/>`_
      ...
    * Concurrency correctness: Octet
    * Concurrency bug detection: Pike, Portend, Cortex, ...
    * Replay debugging: Tardis, rr, RacePro, ...
    * Whole-system determinism: http://dedis.cs.yale.edu/2010/det/

    * Flaky tests

 * Parallelism
    * Languages:
        * Titanium
        * Liquid Metal/Lime
        * Cilk, `Tapir <http://wsmoses.com/tapir.pdf>`_
        * NESL
    * SIMD design space; nested parallelism
 * Incremental/self-adjusting computation: iThreads,
   `Typed Adapton <http://www.cs.cmu.edu/~joshuad/papers/typed-adapton/Hammer17_typed.pdf>`_, etc.

 * Concurrency Bugs:
    * `Notes on Concurrency Bugs <https://danluu.com/concurrency-bugs/>`_
    * https://www.usenix.org/system/files/conference/osdi12/osdi12-final-103.pdf
    * http://mir.cs.illinois.edu/marinov/publications/LinETAL15JaConTeBe.pdf
    * `Learning from Mistakes - A Comprehensive Study on Real World Concurrency Bug Characteristics <https://www.cs.columbia.edu/~junfeng/09fa-e6998/papers/concurrency-bugs.pdf>`_
    * `Finding Concurrency Bugs in Java <http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.58.4088&rep=rep1&type=pdf>`_
    * `Cooperative Concurrency Debugging <http://www.gsd.inesc-id.pt/~ler/reports/nunomachadophd.pdf>`_

 * Memory Models:
    * `SC-Haskell <http://www.cs.indiana.edu/~rrnewton/papers/ppopp17-sc-haskell.pdf>`_
    * `Memory Models: A Case for Rethinking Parallel Languages and Hardware <http://rsim.cs.uiuc.edu/Pubs/10-cacm-memory-models.pdf>`_
    * `DeNovo <http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.659.9703&rep=rep1&type=pdf>`_ and
      `DeNovoND <http://rsim.cs.illinois.edu/denovo/Pubs/13-ASPLOS-denovond.pdf>`_

 * Unsorted:
    * What is the Cost of Weak Determinism? [PACT '14]
    
    * Vats: A Safe, Reactive Storage Abstraction
    * `Shared-Memory Parallelism Can Be Simple, Fast, and Scalable <http://people.eecs.berkeley.edu/~jshun/thesis.pdf>`_
    * `Scalable Non-Zero Indicators <https://hal.inria.fr/hal-01416531/document>`_
    * http://brandonlucia.com/pubs/mspc2014.pdf
    * http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.707.3076&rep=rep1&type=pdf
    * https://people.mpi-sws.org/~orilahav/papers/main.pdf
    * https://core.ac.uk/display/27290446/tab/similar-list
    * https://homes.cs.washington.edu/~djg/theses/devietti-dissertation.pdf
    * http://dpj.cs.illinois.edu/DPJ/Home_files/DPJ-HotPar-2009.html
    * http://goto.ucsd.edu/~rjhala/papers/deterministic_parallelism_via_liquid_effects.pdf


Concurrency Bugs
----------------

* TaxDC: A Taxonomy of Non-Deterministic Concurrency Bugs in Datacenter Distributed Systems: http://ucare.cs.uchicago.edu/pdf/asplos16-TaxDC.pdf
* DCatch: Automatically Detecting Distributed Concurrency Bugs in Cloud Systems: https://people.cs.uchicago.edu/~shanlu/paper/asplos17-preprint.pdf
* What Bugs Live in the Cloud? A Study of 3000+ Issues in Cloud Systems: http://ucare.cs.uchicago.edu/pdf/socc14-cbs.pdf



