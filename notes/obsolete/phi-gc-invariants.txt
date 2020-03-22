CPS and GC Root Invariants
==========================

Consider a CFG like this::

        bb1:
                let x = call f (0)
                do something that may GC
                let z = call g (x)
                ...

In its CPS-ish analogue, we would have::

        bb1:
                call[bb2] f (0)
        bb2(x):
                do something that may GC
                call[bb3] g (x)
        bb3(z): ...

which gets translated to SSA::

        bb1:
                let x.0 = call f (0)
                br bb2
        bb2:
                let x = phi [x.0]
                do something that may GC
                let z = call g (x)
        bb3:     ...

Now account for GC root stack slots in both scenarios::

        bb1:
                let x = call f (0)
                store x to x.gcroot
                do something that may GC
                let x.tmp = load x.groot
                let z = call h (x.tmp)
                ...

versus::

        bb1:
                let x.0 = call f (0)
                store x.0 in x.0.gcroot
                let x.1 = load x.0.gcroot
                br bb2
        bb2:
                let x.p = phi [x.1]
                store x.p into x.p.gcroot
                do something that may GC
                let x.p.tmp = load x.p.gcroot
                let z = call g (x.p.tmp)
        bb3:     ...

The problem here is that we've increased the number of GC roots
by adding one for a phi. But the phi's root is logically unnecessary:
all the phi serves to do is rename x.0 to x.p.
We could try to eliminate the extra gc root::

        bb1:
                let x.0 = call f (0)
                store x.0 in x.0.gcroot
                let x.1 = load x.0.gcroot
                br bb2
        bb2:
                let x.p = phi [x.1]
                do something that may GC
                let z = call g (x.p)
        bb3:     ...

but the problem now is that we're using a potentially-stale value.
If we simplify the above CFG we get this::

        bb1:
                let x.0 = call f (0)
                store x.0 in x.0.gcroot
                let x.p = load x.0.gcroot
                do something that may GC
                let z = call g (x.p)
                ...

Compare this to the original CFG::

        bb1:
                let x = call f (0)
                store x to x.gcroot
                do something that may GC
                let x.tmp = load x.groot
                let z = call h (x.tmp)
                ...

Now we can see that the net effect of the renaming-phi is to move the load
from the root earlier that it would have occurred otherwise.
