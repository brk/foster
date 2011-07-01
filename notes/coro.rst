Coroutine Implementation
========================

A call to ``coro_create`` in Foster gets compiled to
type-specialized code (``CodegenPass:emitCoroCreateFn`` in
``compiler/passes/Codegen/Codegen-coro.cpp``)
which memallocs two coro structs,
which we refer to as an fcoro and a ccoro. The fcoro is
used as the return value of coro_create; the ccoro exists
"behind the scenes", and holds state for internal use by
``coro_yield``. A suspended stack will have pointers into
the stack from both types of coro, but the ccoro pointer
will point higher up the stack::

       +---------------------------+
       |                           |
       |       ...      ...        v
       |        |   f3   | <---  ccoro, site of most
       |        |--------|              recent yield
       |        |   f2   |  stack frames
       v        |--------|  pushed; f1 calls f2, etc
    fcoro ----->|   f1   |
    invoked    ...      ...

Note that the two structs are circularly linked.

We generate a wrapper
function with signature ``void (i8* coro)`` which calls
the coro function, passing it the env and args stored
in the coro struct, and writing the returned values back
into the coro struct, finally marking the coro as dead.
We then call ``foster_coro_create``, passing it the wrapper
and the coro pointer.

``foster_coro_create`` locks a mutex to enforce thread safety.
It then allocates a stack and calls the ``libcoro`` function
``coro_create``. This function, in turn, writes the coro pointer
and wrapper function pointers to statically allocated memory
(thus the mutex) and scribbles the ``libcoro``-internal
``coro_init`` function in a return-address slot of the stack.
Finally, ``coro_transfer`` is called, which switches the stack
pointer to the new stack and "returns" to ``coro_init``.

``coro_init`` then reads the wrapper and coro pointers from
static memory into stack-allocated variables, and executes
another ``coro_transfer`` just before calling the wrapper,
passing it the coro arg. The ``coro_transfer`` leaves the
coro in a dormant state, such that the next ``coro_invoke``
will cause the wrapper to start executing.

A Hidden GC Root
----------------

With the simple approach sketched above, a pointer to a
GC-allocated coro struct is squirreled away in an un-scanned
stack slot. As a result, if a GC is triggered between creating
a coro and invoking it, the pointer to the coro struct will be
stale.

A number of possible solutions present themselves:

* ``coro_init`` could notify the GC of the slot before
  using the arg pointer. But this is a non-solution; is
  only works if there is one GC and no allocation between
  create and invoke.
* The GC could poke its way into the stack and update the
  one hidden slot. This is ugly, error-prone, and architecture-
  specific, because the specific offset of the arg in the
  stack is not portably defined.
* We could add a layer of indirection: stick the coro arg in a
  malloced (stable storage) ref cell, and pass a pointer to the
  coro pointer to ``coro_create``. Meanwhile, also store this
  ref cell pointer in the coro itself, and teach the GC to
  merely update the slot directly accessible from the coro
  struct.

We currently implement option #3.
