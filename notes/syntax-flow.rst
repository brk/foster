Syntax Flow
===========

Functions and Procedures
------------------------

ProtobufIL uses the function type to determine
whether it is dumping a procedure type or a closure
type.

ProtobufToLLExpr calls either markAsProc() or markAsClosure()
as directed by ProtobufIL. This marking determines whether
the type generated is a pointer to a LLVM function,
or a closure struct. This is needed to ensure that the
types of imported functions correspond to their representation
as either bare procedure pointer or closure pointer.

A proc is convertible to a closure, but a closure is not
convertible to a proc (without using a trampoline, which
in turn requires allocating executable memory, a non-portable
operation).

So we must use types to prevent code from passing a closure
where a proc pointer is required.
