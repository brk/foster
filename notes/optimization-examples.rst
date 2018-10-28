Optimization Examples
=====================

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
involved with such shrinking reductions on an immutable graph representation...::

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


LLVM Examples
-------------


When array bounds checks are disabled, these two expressions
are optimized to the same IR by LLVM's CSE.::

    u = foldRange 0 (arrayLength32 sm) 0 { i => u =>
        ci = (a[i] +Word b[i] +Word u);
        unext = addCarryOfWord ci;
        (bitand-Word ci (digitNumBitsMask !)) >^ c[i];
        unext
      };

    u2 = foldRange 0 (arrayLength32 sm) 0 { i => u =>
        (a[i] +Word b[i] +Word u) >^ c[i];
        unext = addCarryOfWord c[i];
        (bitand-Word c[i] (digitNumBitsMask !)) >^ c[i];
        unext
      };

However, when bounds checks are not disabled, ``u2`` will produce
one extra bounds check operation, compared to ``u`` (for the argument to
``addCarryOfWord`` -- LLVM, out of the box, is smart enough to deduce
that the next line's bounds check fails iff the first one does, and can
thus be eliminated).

Siphash Variants
----------------

Continuation-based::

    half-round = { a0 => b => c0 => d => s => t : Int64 => k =>
      a = a0 +Int64 b;
      c = c0 +Int64 d;
      k (rot a 32) (rot-xor b s a) c (rot-xor d t c)
    };

    double-round = { v0 => v1 => v2 => v3 : Int64 => k =>
      half-round v0 v1 v2 v3 13 16 { a0 => b0 => c0 => d0 =>
      half-round c0 b0 a0 d0 17 21 { c1 => b1 => a1 => d1 =>
      half-round a1 b1 c1 d1 13 16 { a2 => b2 => c2 => d2 =>
      half-round c2 b2 a2 d2 17 21 { c3 => b3 => a3 => d3 =>
               k a3 b3 c3 d3
      } } } }
    };

With unboxed tuples::

    half-round-alt = { a0 => b => c0 => d => s => t : Int64 =>
      a = a0 +Int64 b;
      c = c0 +Int64 d;
      prim tuple-unboxed (rot a 32) (rot-xor b s a) c (rot-xor d t c)
    };

    double-round-alt = { v0 => v1 => v2 => v3 : Int64 =>
      let (a0, b0, c0, d0) = half-round-alt v0 v1 v2 v3 13 16;
      let (c1, b1, a1, d1) = half-round-alt c0 b0 a0 d0 17 21;
      let (a2, b2, c2, d2) = half-round-alt a1 b1 c1 d1 13 16;
      let (c3, b3, a3, d3) = half-round-alt c2 b2 a2 d2 17 21;
      prim tuple-unboxed a3 b3 c3 d3
    };

Optimized LLVM IR::

    define internal fastcc i64 @double-round(i64 %"v0!3375", i64 %"v1!3376", i64 %"v2!3377", i64 %"v3!3378", { i64 (i8*, i64, i64, i64, i64)*, i8* }* nocapture readonly %"k!3379") gc "fostergc" {
    entry:
      %"a!3418" = add i64 %"v1!3376", %"v0!3375"                  ; #uses = 3	; i64
      %"c!3419" = add i64 %"v3!3378", %"v2!3377"                  ; #uses = 2	; i64
      %".x!3422" = shl i64 %"a!3418", 32                          ; #uses = 1	; i64
      %".x!3425" = lshr i64 %"a!3418", 32                         ; #uses = 1	; i64
      %".x!3421" = or i64 %".x!3422", %".x!3425"                  ; #uses = 1	; i64
      %".x!3428" = shl i64 %"v1!3376", 13                         ; #uses = 1	; i64
      %".x!3431" = lshr i64 %"v1!3376", 51                        ; #uses = 1	; i64
      %".x!3427" = or i64 %".x!3428", %".x!3431"                  ; #uses = 1	; i64
      %".x!3426" = xor i64 %".x!3427", %"a!3418"                  ; #uses = 3	; i64
      %".x!3434" = shl i64 %"v3!3378", 16                         ; #uses = 1	; i64
      %".x!3437" = lshr i64 %"v3!3378", 48                        ; #uses = 1	; i64
      %".x!3433" = or i64 %".x!3434", %".x!3437"                  ; #uses = 1	; i64
      %".x!3432" = xor i64 %".x!3433", %"c!3419"                  ; #uses = 3	; i64
      %"a!3629" = add i64 %"c!3419", %".x!3426"                   ; #uses = 3	; i64
      %"c!3630" = add i64 %".x!3432", %".x!3421"                  ; #uses = 2	; i64
      %".x!3633" = shl i64 %"a!3629", 32                          ; #uses = 1	; i64
      %".x!3636" = lshr i64 %"a!3629", 32                         ; #uses = 1	; i64
      %".x!3632" = or i64 %".x!3633", %".x!3636"                  ; #uses = 1	; i64
      %".x!3639" = shl i64 %".x!3426", 17                         ; #uses = 1	; i64
      %".x!3642" = lshr i64 %".x!3426", 47                        ; #uses = 1	; i64
      %".x!3638" = or i64 %".x!3639", %".x!3642"                  ; #uses = 1	; i64
      %".x!3637" = xor i64 %".x!3638", %"a!3629"                  ; #uses = 3	; i64
      %".x!3645" = shl i64 %".x!3432", 21                         ; #uses = 1	; i64
      %".x!3648" = lshr i64 %".x!3432", 43                        ; #uses = 1	; i64
      %".x!3644" = or i64 %".x!3645", %".x!3648"                  ; #uses = 1	; i64
      %".x!3643" = xor i64 %".x!3644", %"c!3630"                  ; #uses = 3	; i64
      %"a!3651" = add i64 %"c!3630", %".x!3637"                   ; #uses = 3	; i64
      %"c!3652" = add i64 %".x!3643", %".x!3632"                  ; #uses = 2	; i64
      %".x!3655" = shl i64 %"a!3651", 32                          ; #uses = 1	; i64
      %".x!3658" = lshr i64 %"a!3651", 32                         ; #uses = 1	; i64
      %".x!3654" = or i64 %".x!3655", %".x!3658"                  ; #uses = 1	; i64
      %".x!3661" = shl i64 %".x!3637", 13                         ; #uses = 1	; i64
      %".x!3664" = lshr i64 %".x!3637", 51                        ; #uses = 1	; i64
      %".x!3660" = or i64 %".x!3661", %".x!3664"                  ; #uses = 1	; i64
      %".x!3659" = xor i64 %".x!3660", %"a!3651"                  ; #uses = 3	; i64
      %".x!3667" = shl i64 %".x!3643", 16                         ; #uses = 1	; i64
      %".x!3670" = lshr i64 %".x!3643", 48                        ; #uses = 1	; i64
      %".x!3666" = or i64 %".x!3667", %".x!3670"                  ; #uses = 1	; i64
      %".x!3665" = xor i64 %".x!3666", %"c!3652"                  ; #uses = 3	; i64
      %"a!3673" = add i64 %"c!3652", %".x!3659"                   ; #uses = 3	; i64
      %"c!3674" = add i64 %".x!3665", %".x!3654"                  ; #uses = 2	; i64
      %".x!3677" = shl i64 %"a!3673", 32                          ; #uses = 1	; i64
      %".x!3680" = lshr i64 %"a!3673", 32                         ; #uses = 1	; i64
      %".x!3676" = or i64 %".x!3677", %".x!3680"                  ; #uses = 1	; i64
      %".x!3683" = shl i64 %".x!3659", 17                         ; #uses = 1	; i64
      %".x!3686" = lshr i64 %".x!3659", 47                        ; #uses = 1	; i64
      %".x!3682" = or i64 %".x!3683", %".x!3686"                  ; #uses = 1	; i64
      %".x!3681" = xor i64 %".x!3682", %"a!3673"                  ; #uses = 1	; i64
      %".x!3689" = shl i64 %".x!3665", 21                         ; #uses = 1	; i64
      %".x!3692" = lshr i64 %".x!3665", 43                        ; #uses = 1	; i64
      %".x!3688" = or i64 %".x!3689", %".x!3692"                  ; #uses = 1	; i64
      %".x!3687" = xor i64 %".x!3688", %"c!3674"                  ; #uses = 1	; i64
      %getCloEnv.subgep = getelementptr { i64 (i8*, i64, i64, i64, i64)*, i8* }* %"k!3379", i32 0, i32 1 ; #uses = 1	; i8**
      %getCloEnv.subgep_ld = load i8** %getCloEnv.subgep          ; #uses = 1	; i8*
      %getCloCode.subgep = getelementptr { i64 (i8*, i64, i64, i64, i64)*, i8* }* %"k!3379", i32 0, i32 0 ; #uses = 1	; i64 (i8*, i64, i64, i64, i64)**
      %getCloCode.subgep_ld = load i64 (i8*, i64, i64, i64, i64)** %getCloCode.subgep ; #uses = 1	; i64 (i8*, i64, i64, i64, i64)*
      %".call!14853" = tail call fastcc i64 %getCloCode.subgep_ld(i8* %getCloEnv.subgep_ld, i64 %"c!3674", i64 %".x!3681", i64 %".x!3676", i64 %".x!3687") ; #uses = 1	; i64
      ret i64 %".call!14853"
    }

    define internal fastcc i64 @double-round(i64 %"v0!3375", i64 %"v1!3376", i64 %"v2!3377", i64 %"v3!3378", { i64 (i8*, i64, i64, i64, i64)*, i8* }* nocapture readonly %"k!3379") gc "fostergc" {
    entry:
      %"a!3418" = add i64 %"v1!3376", %"v0!3375"                  ; #uses = 3	; i64
      %"c!3419" = add i64 %"v3!3378", %"v2!3377"                  ; #uses = 2	; i64
      %".x!3422" = shl i64 %"a!3418", 32                          ; #uses = 1	; i64
      %".x!3425" = lshr i64 %"a!3418", 32                         ; #uses = 1	; i64
      %".x!3421" = or i64 %".x!3422", %".x!3425"                  ; #uses = 1	; i64
      %".x!3428" = shl i64 %"v1!3376", 13                         ; #uses = 1	; i64
      %".x!3431" = lshr i64 %"v1!3376", 51                        ; #uses = 1	; i64
      %".x!3427" = or i64 %".x!3428", %".x!3431"                  ; #uses = 1	; i64
      %".x!3426" = xor i64 %".x!3427", %"a!3418"                  ; #uses = 3	; i64
      %".x!3434" = shl i64 %"v3!3378", 16                         ; #uses = 1	; i64
      %".x!3437" = lshr i64 %"v3!3378", 48                        ; #uses = 1	; i64
      %".x!3433" = or i64 %".x!3434", %".x!3437"                  ; #uses = 1	; i64
      %".x!3432" = xor i64 %".x!3433", %"c!3419"                  ; #uses = 3	; i64
      %"a!3629" = add i64 %"c!3419", %".x!3426"                   ; #uses = 3	; i64
      %"c!3630" = add i64 %".x!3432", %".x!3421"                  ; #uses = 2	; i64
      %".x!3633" = shl i64 %"a!3629", 32                          ; #uses = 1	; i64
      %".x!3636" = lshr i64 %"a!3629", 32                         ; #uses = 1	; i64
      %".x!3632" = or i64 %".x!3633", %".x!3636"                  ; #uses = 1	; i64
      %".x!3639" = shl i64 %".x!3426", 17                         ; #uses = 1	; i64
      %".x!3642" = lshr i64 %".x!3426", 47                        ; #uses = 1	; i64
      %".x!3638" = or i64 %".x!3639", %".x!3642"                  ; #uses = 1	; i64
      %".x!3637" = xor i64 %".x!3638", %"a!3629"                  ; #uses = 3	; i64
      %".x!3645" = shl i64 %".x!3432", 21                         ; #uses = 1	; i64
      %".x!3648" = lshr i64 %".x!3432", 43                        ; #uses = 1	; i64
      %".x!3644" = or i64 %".x!3645", %".x!3648"                  ; #uses = 1	; i64
      %".x!3643" = xor i64 %".x!3644", %"c!3630"                  ; #uses = 3	; i64
      %"a!3651" = add i64 %"c!3630", %".x!3637"                   ; #uses = 3	; i64
      %"c!3652" = add i64 %".x!3643", %".x!3632"                  ; #uses = 2	; i64
      %".x!3655" = shl i64 %"a!3651", 32                          ; #uses = 1	; i64
      %".x!3658" = lshr i64 %"a!3651", 32                         ; #uses = 1	; i64
      %".x!3654" = or i64 %".x!3655", %".x!3658"                  ; #uses = 1	; i64
      %".x!3661" = shl i64 %".x!3637", 13                         ; #uses = 1	; i64
      %".x!3664" = lshr i64 %".x!3637", 51                        ; #uses = 1	; i64
      %".x!3660" = or i64 %".x!3661", %".x!3664"                  ; #uses = 1	; i64
      %".x!3659" = xor i64 %".x!3660", %"a!3651"                  ; #uses = 3	; i64
      %".x!3667" = shl i64 %".x!3643", 16                         ; #uses = 1	; i64
      %".x!3670" = lshr i64 %".x!3643", 48                        ; #uses = 1	; i64
      %".x!3666" = or i64 %".x!3667", %".x!3670"                  ; #uses = 1	; i64
      %".x!3665" = xor i64 %".x!3666", %"c!3652"                  ; #uses = 3	; i64
      %"a!3673" = add i64 %"c!3652", %".x!3659"                   ; #uses = 3	; i64
      %"c!3674" = add i64 %".x!3665", %".x!3654"                  ; #uses = 2	; i64
      %".x!3677" = shl i64 %"a!3673", 32                          ; #uses = 1	; i64
      %".x!3680" = lshr i64 %"a!3673", 32                         ; #uses = 1	; i64
      %".x!3676" = or i64 %".x!3677", %".x!3680"                  ; #uses = 1	; i64
      %".x!3683" = shl i64 %".x!3659", 17                         ; #uses = 1	; i64
      %".x!3686" = lshr i64 %".x!3659", 47                        ; #uses = 1	; i64
      %".x!3682" = or i64 %".x!3683", %".x!3686"                  ; #uses = 1	; i64
      %".x!3681" = xor i64 %".x!3682", %"a!3673"                  ; #uses = 1	; i64
      %".x!3689" = shl i64 %".x!3665", 21                         ; #uses = 1	; i64
      %".x!3692" = lshr i64 %".x!3665", 43                        ; #uses = 1	; i64
      %".x!3688" = or i64 %".x!3689", %".x!3692"                  ; #uses = 1	; i64
      %".x!3687" = xor i64 %".x!3688", %"c!3674"                  ; #uses = 1	; i64
      %getCloEnv.subgep = getelementptr { i64 (i8*, i64, i64, i64, i64)*, i8* }* %"k!3379", i32 0, i32 1 ; #uses = 1	; i8**
      %getCloEnv.subgep_ld = load i8** %getCloEnv.subgep          ; #uses = 1	; i8*
      %getCloCode.subgep = getelementptr { i64 (i8*, i64, i64, i64, i64)*, i8* }* %"k!3379", i32 0, i32 0 ; #uses = 1	; i64 (i8*, i64, i64, i64, i64)**
      %getCloCode.subgep_ld = load i64 (i8*, i64, i64, i64, i64)** %getCloCode.subgep ; #uses = 1	; i64 (i8*, i64, i64, i64, i64)*
      %".call!14853" = tail call fastcc i64 %getCloCode.subgep_ld(i8* %getCloEnv.subgep_ld, i64 %"c!3674", i64 %".x!3681", i64 %".x!3676", i64 %".x!3687") ; #uses = 1	; i64
      ret i64 %".call!14853"
    }

Optimized Assembly::

            .align	16, 0x90
            .type	"double-round",@function
    "double-round":                         # @double-round
            .cfi_startproc
    # BB#0:                                 # %entry
            pushl	%ebp
    .Ltmp2:
            .cfi_def_cfa_offset 8
    .Ltmp3:
            .cfi_offset %ebp, -8
            movl	%esp, %ebp
    .Ltmp4:
            .cfi_def_cfa_register %ebp
            pushl	%ebx
            pushl	%edi
            pushl	%esi
            subl	$60, %esp
    .Ltmp5:
            .cfi_offset %esi, -20
    .Ltmp6:
            .cfi_offset %edi, -16
    .Ltmp7:
            .cfi_offset %ebx, -12
            movl	%edx, -20(%ebp)         # 4-byte Spill
            movl	%ecx, %eax
            movl	24(%ebp), %edi
            movl	8(%ebp), %esi
            movl	12(%ebp), %edx
            movl	16(%ebp), %ecx
            movl	%ecx, -16(%ebp)         # 4-byte Spill
            movl	20(%ebp), %ebx
            movl	%edx, %ecx
            addl	%esi, %eax
            movl	%eax, -24(%ebp)         # 4-byte Spill
            adcl	%edx, -20(%ebp)         # 4-byte Folded Spill
            addl	%edi, -16(%ebp)         # 4-byte Folded Spill
            movl	28(%ebp), %edx
            adcl	%edx, %ebx
            movl	%ebx, -28(%ebp)         # 4-byte Spill
            movl	%ebx, %eax
            shldl	$13, %esi, %ecx
            movl	12(%ebp), %ebx
            shldl	$13, %ebx, %esi
            movl	%edx, %ebx
                                            # kill: EDX<def> EBX<kill>
            shldl	$16, %edi, %edx
            shldl	$16, %ebx, %edi
            xorl	-20(%ebp), %ecx         # 4-byte Folded Reload
            movl	%ecx, %ebx
            xorl	-24(%ebp), %esi         # 4-byte Folded Reload
            xorl	%eax, %edx
            movl	-16(%ebp), %eax         # 4-byte Reload
            xorl	%eax, %edi
            addl	%esi, %eax
            movl	%eax, -16(%ebp)         # 4-byte Spill
            movl	-28(%ebp), %eax         # 4-byte Reload
            adcl	%ecx, %eax
            movl	%eax, -28(%ebp)         # 4-byte Spill
            addl	%edi, -20(%ebp)         # 4-byte Folded Spill
            adcl	%edx, -24(%ebp)         # 4-byte Folded Spill
            shldl	$17, %esi, %ebx
            shldl	$17, %ecx, %esi
            movl	%edx, %ecx
            shldl	$21, %edi, %ecx
            shldl	$21, %edx, %edi
            xorl	%eax, %ebx
            movl	%ebx, %eax
            xorl	-16(%ebp), %esi         # 4-byte Folded Reload
            movl	-24(%ebp), %edx         # 4-byte Reload
            xorl	%edx, %ecx
            xorl	-20(%ebp), %edi         # 4-byte Folded Reload
            addl	%esi, -20(%ebp)         # 4-byte Folded Spill
            adcl	%ebx, %edx
            movl	%edx, -24(%ebp)         # 4-byte Spill
            addl	%edi, -28(%ebp)         # 4-byte Folded Spill
            adcl	%ecx, -16(%ebp)         # 4-byte Folded Spill
            shldl	$13, %esi, %eax
            shldl	$13, %ebx, %esi
            movl	%ecx, %edx
            shldl	$16, %edi, %edx
            shldl	$16, %ecx, %edi
            xorl	-24(%ebp), %eax         # 4-byte Folded Reload
            movl	%eax, -32(%ebp)         # 4-byte Spill
            xorl	-20(%ebp), %esi         # 4-byte Folded Reload
            movl	-16(%ebp), %ecx         # 4-byte Reload
            xorl	%ecx, %edx
            movl	-28(%ebp), %ebx         # 4-byte Reload
            xorl	%ebx, %edi
            addl	%esi, %ebx
            movl	%ebx, -28(%ebp)         # 4-byte Spill
            adcl	%eax, %ecx
            movl	%ecx, -16(%ebp)         # 4-byte Spill
            movl	%eax, %ecx
            addl	%edi, -24(%ebp)         # 4-byte Folded Spill
            movl	-20(%ebp), %ebx         # 4-byte Reload
            adcl	%edx, %ebx
            movl	-32(%ebp), %eax         # 4-byte Reload
            shldl	$17, %esi, %eax
            shldl	$17, %ecx, %esi
            movl	%edx, %ecx
            shldl	$21, %edi, %ecx
            shldl	$21, %edx, %edi
            movl	32(%ebp), %edx
            movl	4(%edx), %edx
            movl	%edx, -20(%ebp)         # 4-byte Spill
            movl	-28(%ebp), %edx         # 4-byte Reload
            xorl	%edx, %esi
            xorl	-16(%ebp), %eax         # 4-byte Folded Reload
            movl	%eax, -32(%ebp)         # 4-byte Spill
            xorl	%ebx, %ecx
            movl	-24(%ebp), %eax         # 4-byte Reload
            xorl	%eax, %edi
            movl	%edx, 16(%esp)
            movl	-16(%ebp), %edx         # 4-byte Reload
            movl	%edx, 12(%esp)
            movl	%ebx, (%esp)
            movl	%ecx, 24(%esp)
            movl	%edi, 20(%esp)
            movl	-32(%ebp), %ecx         # 4-byte Reload
            movl	%ecx, 8(%esp)
            movl	%esi, 4(%esp)
            movl	-20(%ebp), %ecx         # 4-byte Reload
            movl	%eax, %edx
            movl	32(%ebp), %eax
            calll	*(%eax)
    .Ltmp1:
            addl	$60, %esp
            popl	%esi
            popl	%edi
            popl	%ebx
            popl	%ebp
            retl
    .Ltmp8:
            .size	"double-round", .Ltmp8-"double-round"
            .cfi_endproc

            .align	16, 0x90
            .type	"double-round-alt",@function
    "double-round-alt":                     # @double-round-alt
    # BB#0:                                 # %entry
            pushl	%ebp
            movl	%esp, %ebp
            pushl	%ebx
            pushl	%edi
            pushl	%esi
            subl	$24, %esp
            movl	%edx, %ebx
            movl	%ecx, -32(%ebp)         # 4-byte Spill
            movl	28(%ebp), %esi
            movl	12(%ebp), %eax
            movl	16(%ebp), %ecx
            movl	20(%ebp), %edi
            movl	24(%ebp), %edx
            movl	%edx, -20(%ebp)         # 4-byte Spill
            movl	%ecx, %edx
            addl	%eax, %ebx
            movl	%ebx, -28(%ebp)         # 4-byte Spill
            movl	8(%ebp), %ebx
            adcl	%ecx, %ebx
            movl	%ebx, -24(%ebp)         # 4-byte Spill
            addl	%esi, %edi
            movl	%edi, -16(%ebp)         # 4-byte Spill
            movl	-20(%ebp), %edi         # 4-byte Reload
            adcl	32(%ebp), %edi
            movl	%edi, -20(%ebp)         # 4-byte Spill
            shldl	$13, %eax, %edx
            shldl	$13, %ecx, %eax
            movl	32(%ebp), %edi
            shldl	$16, %esi, %edi
            movl	32(%ebp), %ecx
            shldl	$16, %ecx, %esi
            xorl	%ebx, %edx
            movl	%edx, -36(%ebp)         # 4-byte Spill
            xorl	-28(%ebp), %eax         # 4-byte Folded Reload
            movl	-20(%ebp), %ebx         # 4-byte Reload
            xorl	%ebx, %edi
            movl	-16(%ebp), %ecx         # 4-byte Reload
            xorl	%ecx, %esi
            addl	%eax, %ecx
            movl	%ecx, -16(%ebp)         # 4-byte Spill
            adcl	%edx, %ebx
            addl	%esi, -24(%ebp)         # 4-byte Folded Spill
            adcl	%edi, -28(%ebp)         # 4-byte Folded Spill
            movl	-36(%ebp), %ecx         # 4-byte Reload
            shldl	$17, %eax, %ecx
            shldl	$17, %edx, %eax
            movl	%edi, %edx
            shldl	$21, %esi, %edx
            shldl	$21, %edi, %esi
            xorl	%ebx, %ecx
            movl	%ecx, -36(%ebp)         # 4-byte Spill
            movl	%ecx, %edi
            xorl	-16(%ebp), %eax         # 4-byte Folded Reload
            movl	-28(%ebp), %ecx         # 4-byte Reload
            xorl	%ecx, %edx
            xorl	-24(%ebp), %esi         # 4-byte Folded Reload
            addl	%eax, -24(%ebp)         # 4-byte Folded Spill
            adcl	%edi, %ecx
            movl	%ecx, -28(%ebp)         # 4-byte Spill
            addl	%esi, %ebx
            movl	%ebx, -20(%ebp)         # 4-byte Spill
            adcl	%edx, -16(%ebp)         # 4-byte Folded Spill
            movl	-36(%ebp), %ebx         # 4-byte Reload
            shldl	$13, %eax, %ebx
            shldl	$13, %edi, %eax
            movl	%edx, %edi
            shldl	$16, %esi, %edi
            shldl	$16, %edx, %esi
            xorl	%ecx, %ebx
            movl	%ebx, -36(%ebp)         # 4-byte Spill
            movl	-24(%ebp), %edx         # 4-byte Reload
            xorl	%edx, %eax
            xorl	-16(%ebp), %edi         # 4-byte Folded Reload
            movl	-20(%ebp), %ecx         # 4-byte Reload
            xorl	%ecx, %esi
            addl	%eax, %ecx
            movl	%ecx, -20(%ebp)         # 4-byte Spill
            adcl	%ebx, -16(%ebp)         # 4-byte Folded Spill
            addl	%esi, -28(%ebp)         # 4-byte Folded Spill
            adcl	%edi, %edx
            movl	%edx, -24(%ebp)         # 4-byte Spill
            movl	-36(%ebp), %edx         # 4-byte Reload
            shldl	$17, %eax, %edx
            shldl	$17, %ebx, %eax
            movl	%edi, %ecx
            shldl	$21, %esi, %ecx
            shldl	$21, %edi, %esi
            movl	-20(%ebp), %ebx         # 4-byte Reload
            xorl	%ebx, %eax
            movl	-32(%ebp), %edi         # 4-byte Reload
            movl	%ebx, 20(%edi)
            movl	-28(%ebp), %ebx         # 4-byte Reload
            xorl	%ebx, %esi
            movl	%ebx, (%edi)
            movl	-16(%ebp), %ebx         # 4-byte Reload
            xorl	%ebx, %edx
            movl	%ebx, 16(%edi)
            movl	-24(%ebp), %ebx         # 4-byte Reload
            xorl	%ebx, %ecx
            movl	%ebx, 4(%edi)
            movl	%ecx, 28(%edi)
            movl	%esi, 24(%edi)
            movl	%edx, 12(%edi)
            movl	%eax, 8(%edi)
            addl	$24, %esp
            popl	%esi
            popl	%edi
            popl	%ebx
            popl	%ebp
            retl
    .Ltmp9:
            .size	"double-round-alt", .Ltmp9-"double-round-alt"

The generated assembly is not identical, but it is very similar.
LLVM can inline the unboxed example but requires source-level inlining to
generate allocation-free code for the continuation-based variant.
