In Haskell, Int is defined in such a way that it can be implemented via
bit-stealing of a machine word on 32-bit platforms.
This means that CInt must be a separate type.

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
pointers, void, void*) in Foster?
