The typing rule for effect handlers (without the ``as`` clause,
and ignoring the type of ``resume`` for now, is::

    e    : { r @ (eff|effs) }
    arm* : { Eff => r @ effs }
    -------------------------
    HANDLE e arms END : r @ effs

The idea being that ``e``, which might have multiple effects,
gets just one of the effects handled by each ``handle`` expression.

Consider code like the following::

    handle E of
      Op1 -> 42
      Op2 -> resume 42
      Op3 -> print 1; resume 2; print 3
      Op4 -> save resume
    end


What happens at run time? A simple story is that we create a coroutine for the expression ``E``,
and invoke it. A ``yield`` expression corresponds to a coro yield. Any yielded values (representing
effects to be handled) are passed to a ``case`` expression with the arms.

Now, what should the type of ``resume`` be? Assuming the active arm is for an effect declared
as ``Opx foo => bar``:

* If it is ``{ bar => r @ effs }`` then we have implicitly
  tied the computation E to the handler expression.
  This is not so good because it means that we've lost modularity between schedulers, for example.
* If it is ``{ bar => r @ (eff|effs) }`` then calls to ``resume`` in the handler arms are ill-typed
  since there's (again, implicitly) no recurring back to the same handler for the next yield.