Closure Conversion
------------------

Consider the following example of (supposedly) mutually
recursive functions::

    let n = 0; in
      rec f = { x => g x; h };
          g = { y => h y; };
          h = { z => print n; };
      in
        f !;
      end
    end

Closure conversion produces the following::

    procF = { env x => case env of (envG, g, envH, h) ->
                         procG envG x; h
                        end };
    procG = { env y => case env of (envH, h) ->
                         procH envH y;
                       end };
    procH = { env z => case env of (n) ->
                         print n;
                       end };

    let n = 0; in
      CLO f = CLOSURE procF env0 [env1, env2, h];
          g = CLOSURE procG env1 [env2, h];
          h = CLOSURE procH env2 [n];
      in
        f !;
      end
    end

Things to note about the transformation:

#. The call to ``g`` inside ``f`` is known, and therefore ``f`` only
   needs g's environment -- not ``g``'s closure -- to call ``g``.
#. But ``f`` returns ``h``, rather than calling it, so to avoid
   allocating a new closure every time ``f`` is called,
   ``f`` captures ``h`` (that is, the closure) directly.
#. The closure for ``f`` captures ``h``, ``g``, and the two associated
   environments. Capturing ``g`` and ``envH`` could be avoided with
   more analysis.
#. The call to ``f`` underneath the ``CLO`` node isn't changed;
   calls to procedures and closures aren't differentiated
   until the code hits LLVM.
#. The binding structure of ``CLO`` is pretty strange: it binds
   ``f``, ``g``, and ``h`` (recursively), but it *also* binds their
   environment variables recursively!

The next question is, how does CLO get lowered when it hits
LLVM?

First, we allocate storage for the environments (these environments
are unrelated to those above)::

    envSlots:
        [envptr0] -> [ / | / | / ]
        [envptr1] -> [ / | / | / | / | / ]
        [envptr2] -> [ / | / ]

Second, we allocate storage for the closures, and load them with the
env pointers from step 1. We must be careful to not use a stale env
pointer if heap-allocating a closure pair results in a garbage collection.
Thus we first emit code to allocate  a closure pair, and only then do we
load from the env slot to get the envptr that needs to go in the closure::

    closures:
        [clo0] -> [ code0 | envptr0 ]
        [clo1] -> [ code1 | envptr1 ]
        [clo2] -> [ code2 | envptr2 ]

Third, we fill the environment slots by codegenning each environment.
Now each environment can refer to the heap-allocated closures that will
eventually contain them, as well as other environment pointers::

    envSlots:
        [envptr0] -> [ a | b | c ]
        [envptr1] -> [ d | e | f | g | h ]
        [envptr2] -> [ i | j ]


