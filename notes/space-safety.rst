Space Safety
============

Appel & Shao identify *space safety* as an important consideration for
implementations of languages which do not allow manual memory management.

They note that flat closures are safe for space by construction, but may
involve copying more variables than needed.
**Do they have empirical evidence supporting this claim?**

They also say that stack allocation of closures violates SSC "because
dead local variables remain in the stack frame until the function returns."
They say this can be "partially" fixed by informing the GC of which variables
are dead and should be ignored. Another approach (which they don't mention?)
is to explicitly null out dead variables.

One example they give of a problematic function is::

        fun f(h, u, v, w) =
          let fun g() =
            let val x = h (u, v)
                val y = h (x, v)
                val z = h (y, w)
                in z end
            in g end

``g``'s closure contains ``h``, ``u``, ``v``, and ``w``.

        "Under the standard stack implementation, ``g``'s frame would contain a
        pointer to ``h``'s closure, and all four varaibles are kept live until
        ``g`` returns. But variable ``u`` reaches its last use at the first call
        to ``h``; keeping it live with the rest of the closure is clearly not
        space safe."

With flat closure conversion, ``f`` would not retain any variables; they would
all be copied into ``g``'s closure. However, There things get a bit subtler.
When ``g`` is called, it copies out the contents of its closure into its stack
frame. Killing the slots in the stack frame won't help, because the environment
will keep the pointed-to objects live. Killing the environment pointer after
copying out its contents **also** won't help, because the caller of ``g``, who
provided the environment pointer in the first place, has a copy of ``g``'s
closure with the environment pointer. Thus ``g`` must cooperate with its caller
to ensure space safety.

Block Sinking
-------------

In theory, block sinking of functions which do not get contified can change
the allocation rate of programs (for the worse) by moving functions into
more deeply nested scopes which are evaluated more often. I don't think there
has been any published empirical evidence of whether this occurs in practice
or not.
