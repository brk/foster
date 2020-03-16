


Performance-related notes
-------------------------

* The middle-end compiler takes 2m2s to build with -O2, and roughly 48s to build without optimization.
  The middle-end then runs about 30% faster, but serialization time is not affected at all.

* In a hello-world comparison, the foster binary is ~53KB bigger than the C binary.
  Use of ``strings`` suggests strings account for 14KB of the size increase.
  Foster-generated binaries dynamically link against a minimial selection of "standard" libraries:
  libc, libm, librt, pthreads, libgcc_s, and libstdc++

* fannkuchredux(-nogc)-unchecked
    runs 100% slower than the reference C program.
  fannkuchredux-alt with "optimized" GC roots/reloads (and kills)
    runs 42% slower than the reference C program.
  fannkuchredux-alt with "un-optimized" GC roots/reloads (and no kills)
    runs 28% slower than the reference C program. (!)
      The program executes more instructions, but has higher IPC and lower cycle count.
      This suggests that dataflow-driven nulling-out of root slots
      carries non-trivial costs on modern out-of-order machines.
  fannkuchredux-alt with "optimized" GC roots and no reloads (--non-moving-gc)
    runs 10% slower than the reference C program.
  fannkuchredux-alt with "un-optimized" GC roots and no reloads (--non-moving-gc)
    runs 5% slower than the reference C program.
  fannkuchredux-alt with "un-optimized" GC roots and no reloads (--non-moving-gc)
                                            and array bounds checks disabled
    runs 5% FASTER than the reference C program.
  fannkuchredux-alt with no GC roots at all and array bounds checks disabled
    runs 8% FASTER than the reference C program.
