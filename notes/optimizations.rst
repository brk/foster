Optimizations
-------------



GC Optimizations
~~~~~~~~~~~~~~~~

Liveness allows optimizing use of gc roots::

        // IN: 2 3 5 8 13 21

        // * If a function body cannot trigger GC, then the in-params
        //   need not be stored in gcroot slots. Reason: the params
        //   are never live after a GC point, because there are no GC points.
        //
        fn-no-gc = fn (n : i32, r : ref i32) {
          expect_i32(deref(r))
          print_i32(n)
        }

        may-trigger-gc = fn (to i32) { let x : ref i32 = new 0 in { deref(x) } }

        // * If there are no GC points after a `new`, then the returned
        //   pointer need not be stored in a gcroot slot. Reason: there
        //   are no further GC roots across which the pointer must be stored.
        //
        // TODO enable once regular local vars are implemented
        //no-gc-after-new = fn (to i32) {
        //  may-trigger-gc()
        //
        //  let n : ref i32 = new 0 in {
        //    0
        //  }
        //}

        // * If a pointer is dead after being passed to a function,
        //   then it need not exist in a gcroot slot after the previous
        //   GC point. Thus the temporary in `f(new blah)` need not be
        //   stored in a gcroot slot. Reason: not live for GC.
        //
        no-root-for-dead-ptrs = fn () {
          expect_i32(42)
          print_i32(deref(new 42))
        }
        main = fn () {
          fn-no-gc(30, new 30)
          //no-gc-after-new()
          no-root-for-dead-ptrs()
        }

Data Structure Elimination
~~~~~~~~~~~~~~~~~~~~~~~~~~

The following idioms should not involve runtime allocation::

        case (x, ..., x) of ... end

        let v = (x, ..., x) in case v of ... end end
