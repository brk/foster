In Haskell, ``Int`` is defined in such a way that it can be implemented via
bit-stealing of a machine word on 32-bit platforms.
This means that ``CInt`` must be a separate type.

Different languages have different naming conventions. C gets by with
simple symbol names (plus a calling convention).
Other languages like C++ and Java may require
mangled and/or qualified names. I think it makes sense to limit direct
language integration to C; other languages can and should interoperate
via better-defined interfaces, such as protocol buffers.

Thanks to LLVM and Clang, we can focus on interoperating with the LLVM IR
representation of C code, rather than the platform-specific assembly-level
representation. The downside, of course, is that we must
interoperate with a specific compiler's lowering of C to
LLVM IR, and different compilers lower in different ways.
For expedience, we can start by focusing only on Clang.

The question is then: how can we unambiguously represent
C-compatible types (for, let's say, the integral types, pointers, function
pointers, ``void``, ``void*``) in Foster?

Clang Struct Lowerings
----------------------

Clang and llvm-gcc do not always lower struct types identically, and
the LLVM generated does not always correspond to the most straightforward
examples.

On a 64-bit machine, where ``int`` is lowered to ``i32``,
a ``struct { int; }`` is lowered to ``i32`` or ``i64`` by llvm-g++,
and to ``i64`` by clang++.

``type { i32, i8, i8 }`` is lowered by both llvm-g++ and clang++ as ``i64``.

``type { i32, i8, i8, i32, i32 }`` is returned by llvm-g++ as
``type { i64, i64 }``, while it is passed as two separate ``i64`` values.
Clang at least has the decency to lower both uses to ``type { i64, i64 }``.

``type { i32, i32, i32, i32, i32, i32, i32, i32, i32 }`` is lowered by llvm-g++
and Clang via sret/byval pointers, as is ``type { i8, double, i16 }``. llvm-g++
uses individual store operations, whereas Clang uses memcpy before returning to
write the sret value. Meanwhile, ``type { i8, i16, double }`` is lowered by both
Clang and llvm-g++ to ``type { i64, double }``, passed directly by value in both
directions.

Proposed reverse-engineered lowering rules:

#. Use the standard C alignment rules to calculate the size and offsets for each
   structure field.
#. If the size of the structure fits within a native machine word, lower
   the struct to a machine word.
#. If no field of the structure crosses a machine word boundary, and the size
   of the struct is at most two machine words,
   lower the struct to a pair of machine words. Use integer or floating-point
   types as dicated by the original source: ``double`` becomes ``double``,
   ``2 x float`` becomes ``double``,
   any combination of integer + float types becomes integer.
#. Otherwise, pass the struct via sret/byval parameters.
