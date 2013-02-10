Trivial Cont Eta-Elimination::

        |------------------------------------------| |------------------------------------------|
        |    ret k = (rk,L9)                       | |    ret k = (rk,L9)                       |
        |    entry = (postalloca,L8)               | |    entry = (postalloca,L8)               |
        |    ------------------------------        | |    ------------------------------        |
        |                                          | |                                          |
        |call_cont.L20 [call_res!21]               | |call_cont.L20 [call_res!21]               |
        |cont case_cont.L17 [call_res!21]          | |cont case_cont.L17 [call_res!21]          |
        |                                          | |                                          |
        |call_cont.L18 [call_res!19]               | |call_cont.L18 [call_res!19]               |
        |cont case_cont.L17 [call_res!19]          | |cont case_cont.L17 [call_res!19]          |
        |                                          | |                                          |
        |------------------------------------------| |------------------------------------------|
        |------------------------------------------| |------------------------------------------|
        |                                          | |                                          |
        |case_arm.L16 []                           | |case_arm.L16 []                           |
        |call call_cont.L20 f!3 []                 | |call case_cont.L17 f!3 []                 |
        |                                          | |                                          |
        |case_arm.L15 []                           | |case_arm.L15 []                           |
        |call call_cont.L18 f!3 []                 | |call case_cont.L17 f!3 []                 |
        |                                          | |                                          |
        |------------------------------------------| |------------------------------------------|
        |(no other appearances of L20 or L18)      | |------------------------------------------|
        |------------------------------------------| |------------------------------------------|


Because ``call_cont.L20`` just forwards its argument to ``case_cont.L17``,
every use of the former can be replaced with the latter.

Contification::

        |------------------------------------------| |-----------------------------------------|
        |    ret k = (rk,L9)                       | |    ret k = (rk,L9)                      |
        |    entry = (postalloca,L8)               | |    entry = (postalloca,L8)              |
        |    ------------------------------        | |    ------------------------------       |
        ........................................................................................
        |                                          | |                                         |
        |case_arm.L16 []                           | |case_arm.L16 []                          |
        |call case_cont.L17 f!3 []                 | |cont contified_postalloca.L10 []         |
        |                                          | |                                         |
        |case_arm.L15 []                           | |case_arm.L15 []                          |
        |call case_cont.L17 f!3 []                 | |cont contified_postalloca.L10 []         |
        |                                          | |                                         |
        |postalloca.L8 []                          | |postalloca.L8 []                         |
        |    let v!2 = 0                           | |    let v!2 = 0                          |
        |    fun f!3 = {                           | |cont hoopl.br.L23 []                     |
        |            ret k = (rk,L11)              |
        |            entry = (postalloca,L10)      |
        |            ------------------------------|
        |                                          |
        |        postalloca.L10 []                 | |contified_postalloca.L10 []              |
        |        cont rk.L11 [v!2]                 | |cont case_cont.L17 [v!2]                 |
        |    }[UsedSecondClass]                    |
        |                                          |
        |                                          | |hoopl.br.L23 []                          |
        |    let .x!0 = 0                          | |    let .x!0 = 0                         |
        |    let .seq!4 = prim expect_i32 .x!0     | |    let .seq!4 = prim expect_i32 .x!0    |
        |    let .x!1 = True                       | |    let .x!1 = True                      |
        |case .x!1                                 | |case .x!1                                |
        |  of True                 -> case_arm.L15 | |  of True                 -> case_arm.L15|
        |  of False                -> case_arm.L16 | |  of False                -> case_arm.L16|
        |------------------------------------------| |                                         |

Every call to ``f!3`` above has the same continuation argument (``L17``) so
we can make a copy of ``f!3``'s body (which, note, still closes over ``v!2``).
The copy is called ``contified_postalloca.L10`` and we've substituted the
constant continuation argument for the function's formal continuation argument.
We also changed all the call sites to call ``L10`` instead of ``f!3``.

This optimization is implemented monolithically, because Hoopl doesn't seem to
allow the insertion of a temporarily-disconnected subgraph---it gets
automatically discarded. We restrict this optimization to apply only to
functions which are only used second-class (i.e. called, not passed around),
and combine the rewriting with dead-code elimination, which means we don't need
to re-label or rename anything.

Replacing the call sites with continuations has enabled another optimization:
we can replace ``case_arm!L15`` with ``contified_postalloca.L10`` in the switch.
We could also optimize to either one of::

     |-----------------------------------------|   |-----------------------------------------|
     |    ret k = (rk,L9)                      |   |    ret k = (rk,L9)                      |
     |    entry = (postalloca,L8)              |   |    entry = (postalloca,L8)              |
     |    ------------------------------       |   |    ------------------------------       |
     |case_cont.L17 [.x!2]                     |   |contified_postalloca.L10 []              |
     |    let .seq!5 = prim print_i32 .x!2     |   |    let .seq!5 = prim print_i32  v!2     |
     |    let .seq!6 = ()                      |   |    let .seq!6 = ()                      |
     |    let .cfg_seq!22 = ()                 |   |    let .cfg_seq!22 = ()                 |
     |cont rk.L9 []                            |   |cont rk.L9 []                            |
     ...........................................   ...........................................
     |                                         |   |                                         |
     |case_arm.L16 []                          |   |case_arm.L16 []                          |
     |cont case_cont.L17 [v!2]                 |   |cont contified_postalloca.L10 []         |
     |                                         |   |                                         |
     |case_arm.L15 []                          |   |case_arm.L15 []                          |
     |cont case_cont.L17 [v!2]                 |   |cont contified_postalloca.L10 []         |
     |                                         |   |                                         |
     |postalloca.L8 []                         |   |postalloca.L8 []                         |
     |    let v!2 = 0                          |   |    let v!2 = 0                          |
     |cont hoopl.br.L23 []                     |   |cont hoopl.br.L23 []                     |
     |                                         |   |                                         |
     |contified_postalloca.L10 [] (now dead)   |
     |cont case_cont.L17 [v!2]                 |
     |                                         |   |                                         |
     |hoopl.br.L23 []                          |   |hoopl.br.L23 []                          |
     |    let .x!0 = 0                         |   |    let .x!0 = 0                         |
     |    let .seq!4 = prim expect_i32 .x!0    |   |    let .seq!4 = prim expect_i32 .x!0    |
     |    let .x!1 = True                      |   |    let .x!1 = True                      |
     |case .x!1                                |   |case .x!1                                |
     |  of True                 -> case_arm.L15|   |  of True                 -> case_arm.L15|
     |  of False                -> case_arm.L16|   |  of False                -> case_arm.L16|
     |-----------------------------------------|   |-----------------------------------------|
     (by reasoning that  ``cont c_p.L10 []``       (by reasoning that the only parameter to
      can be replaced by ``cont c_c.L17 [v!2]``)    ``.x!2`` is ``v!2``, so we can subst and
                                                    merge the adjacent continuations)

Note that if the two arms of the case had yielded different results instead of
both passing v2 to L17, then only the former rewrite would be valid.
Also, given the former, we can optimize it to the latter, by noting that every
value passed to .x!2 is v!2 and thus substituting v2 for .x2 everywhere;
.x2 then becomes dead.

I think the Hoopl style is to make a new copy of case_cont.L17 without the extra
param, then rewrite all the call sites to drop the param, then rely on the
implicit CFG simplification to kill the old block. Unfortunately this does break
the unique-naming invariant---temporarily if the old block is truly discarded,
or permanently if it is not..

Combined Beta-Eta For Continuation Application::

    |k0:[]            |   =>   |k0:[]            |
    |cont j [a, b]    |   =>   |cont c [b, z, a] |
    |                 |   =>   |                 |
    |k1:[]            |   =>   |k1:[]            |
    |cont j [d, c]    |   =>   |cont c [c, z, d] |
    |                 |   =>
    |j: [x, y]        |   =>
    |cont c [y, z, x] |   =>

    The eta-cont rule is   letcont k x = j x in C      --> C  [j/k]
    The beta-cont rule is  letcont k x = K   in C[k y] --> C[K[y/x]]

    The example above amounts to
                           letcont k x_ = j y_ in C[k z_] --> C[j [z_/x_]]

    The cont-cont elim pass would map j to c, along with a function
    to accept the actual arguments to the continuation and rename them
    appropriately.

    In the k0/k1 example, it looks like we can get away with just substituting
    the actuals for the formals in the continuation parameters, but we must
    actually do that subsitution over the whole continuation (i.e. C).

    AFAIK we don't currently handle this case, due to the unpleasantness
    involved with such shrinking reductions on an immutable graph representation...

|---------------------------------------| |---------------------------------------|
|    ret k = (rk,L47)                   | |    ret k = (rk,L47)                   |
|    entry = (postalloca,L46)           | |    entry = (postalloca,L46)           |
|    ------------------------------     | |    ------------------------------     |
|                                       | |                                       |
|hoopl.br.L66 []                        | |hoopl.br.L66 []                        |
|    let .x!8 = 4                       | |    let .x!8 = 4                       |
|    let .x!13 = prim - .x!8 a!9        | |    let .x!13 = prim - .x!8 a!9        |
|cont contified_postalloca.L48 [.x!13]  | |cont hoopl.br.L62 []                   |

|contified_postalloca.L48 [x!12]        |
|cont hoopl.br.L62 []                   |

|                                       | |                                       |
|hoopl.br.L62 []                        | |hoopl.br.L62 []                        |
|    let .x!9 = 3                       | |    let .x!9 = 3                       |
|    let .x!12 = prim + b!10 .x!9       | |    let .x!12 = prim + b!10 .x!9       |
|cont hoopl.br.L58 []                   | |cont hoopl.br.L58 []                   |
|                                       | |                                       |
|hoopl.br.L58 []                        | |hoopl.br.L58 []                        |
|    let .x!11 = prim * x!12 c!11       | |    let .x!11 = prim * x!12 c!11       |
|cont contified_postalloca.L52 [.x!11]  | |cont contified_postalloca.L52 [.x!11]  |
|                                       | |                                       |
|contified_postalloca.L52 [z!14]        | |contified_postalloca.L52 [z!14]        |
|    let .x!10 = prim * x!12 y!13       | |    let .x!10 = prim * x!12 y!13       |
|    let .cfg_seq!54 = prim + .x!10 z!14| |    let .cfg_seq!54 = prim + .x!10 z!14|
|cont rk.L47 [.cfg_seq!54]              | |cont rk.L47 [.cfg_seq!54]              |
|                                       | |                                       |
|contified_postalloca.L50 [y!13]        | |contified_postalloca.L48 [x!12]        |
|cont hoopl.br.L58 []                   | |cont hoopl.br.L62 []                   |
|                                       | |                                       |
|contified_postalloca.L48 [x!12]        | |postalloca.L46 [a!9,b!10,c!11]         |
|cont hoopl.br.L62 []                   | |cont hoopl.br.L66 []                   |
|                                       | |        (stage 4)                      |
|postalloca.L46 [a!9,b!10,c!11]         | |---------------------------------------|
|cont hoopl.br.L66 []                   |
|        (stage 3)                      |
|---------------------------------------|






















