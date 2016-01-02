Compiler Overview
=================

In broad strokes:

* ``grammar/foster.g`` defines an ANTLR 3 grammar for Foster,
  which is compiled using ANTLR's C backend. The resulting code
  is linked into ``compiler/fosterparse.cpp``, which is responsible for taking
  a source file, collecting its dependencies, and emitting the ANTLR-generated
  parsed source trees for the collected files (in CBOR format).
* The middle-end, in ``compiler/foster/me/``, goes from parsed source to a
  low-level IR that is almost, but not quite, LLVM. The middle end performs
  type inference, monomorphization, inlining, pattern match compilation,
  closure conversion, lambda lifting, optimized GC root insertion, and data
  constructor representation selection. The middle end also contains a reference
  interpreter implementation. The flow through the middle end is roughly as follows:

  * ``cb_parseWholeProgram`` converts a CBOR-encoding ByteString and builds a
    ``WholeProgramAST FnAST TypeP``.
  * ``compile`` stitches together the pieces of the compiler:

    * ``desugarParsedModule`` converts "parsed types" ``TypeP`` into ``TypeAST``;
      the main differences are that kinds are required on ForAlls,
      functions get effect parameters, and built-in type constructor names are
      recognized & mapped to the "native" constructors.
    * Typechecking/inference converts
      ``ExprAST :: TypeAST`` to ``AnnExpr :: TypeTC``,
      operating on SCCs of functions.
      Notable changes in expr structure: switch from ``EPattern`` to ``Pattern``;
      nests of recursive fns/exprs are rearranged to form SCCs; sequencing
      is replaced with fresh bindings; constructor applications are split out
      from non-constructor applications; type ascriptions are eliminated.
      Notable changes in type structure: inference of boxed vs unboxed tuples;
      elimination of meta-type-placeholders.
    * Afterwards, ``convertTypeILofAST``
      goes to ``ModuleIL AIExpr TypeIL``, which represents the module's
      value-level contents as an expression rather than a list of functions.
      The primary type-level differences are elimination of unification vars
      and ref types, and introduction of pointer types.
      Expr-level differences: removing non-call uses of primitive exprs, and
      all lambdas must be let/rec bound.
      This stage also assigns types to integer constants, determines where to
      store array literals, assigns constructor representations,
      and checks for (some) inappropriate uses of
      unboxed polymorphism.
    * The ``ModuleIL`` is then subject to lowering, which consists of:

      * K-normalization
      * Monomorphization
      * Static checking of refinement types
      * Loop header insertion
      * Shrinking
      * Inlining
      * Block sinking
      * CFG construction
      * CFG simplification & contification
      * May-GC analysis
      * Closure conversion and pattern-match compilation.
      * Allocation explication
      * GC root insertion
      * And finally, conversion to the output protocol buffers
* The backend is composed of two executables:

  * ``compiler/fosterlower.cpp`` takes the protocol-buffer-encoded IR from the
    middle end and emits the appropriate LLVM IR. Having this functionality
    implemented in C++ makes it easier to interoprerate with the LLVM API.
    The codegen process does a bunch of miscellaneous extra work, including
    lazy generation of coroutine wrappers, decision tree occurrence indexing,
    lazy type map generation, and some function argument coercion.
  * ``compiler/fosteroptc.cpp`` takes LLVM IR and compiles it down to assembly
    or object code. It does the same work as ``llc`` and ``optc``, but it runs
    Foster-specific optimization passes and uses a custom GC plugin for
    emitting stack maps in a format the runtime can understand.
* ``scripts/fosterc.py`` ties the above processes together, and handles
  platform-specific linking details. It is in turn wrapped by
  ``scripts/runtest.py``.

.. graphviz::

   digraph compileroverview {
      "ModuleAST TypeAST" -> "AnnExpr TypeTC";
      "AnnExpr TypeTC" -> "AnnExprIL TypeIL";
      "AnnExprIL TypeIL" -> "AIExpr TypeIL";
      "AIExpr TypeIL" -> "KNExpr TypeIL" [label=" kNormalizeModule"];
      "KNExpr TypeIL" -> "(KNExpr' RecStatus MonoType) MonoType" [label=" monomorphize"];
      "(KNExpr' RecStatus MonoType) MonoType" -> "(KNExpr' RecStatus MonoType) MonoType" [label=" runStaticChecks"];
      "(KNExpr' RecStatus MonoType) MonoType" -> "(KNExpr' RecStatus MonoType) MonoType'" [label=" knLoopHeaders"];
      "(KNExpr' RecStatus MonoType) MonoType'" -> "(KNExpr' RecStatus MonoType) MonoType''" [label=" knInline, knSinkBlocks"];
      "(KNExpr' RecStatus MonoType) MonoType''" -> "CFBody MonoType" [label=" cfg-ize"];
      "CFBody MonoType" -> "CCBody TypeLL" [label=" closureConvertAndLift"];
      "CCBody TypeLL" -> "..." [label=" prepForCodegen, etc"];
   }

Pass Ordering Issues
====================

* Inlining is improved when loop headers are inserted earlier, because it's
  generally more profitable to specialize a loop rather than unroll it once.
  But the decision of whether a particular recursive call should become a
  call to the loop header or the original function is improved when the results
  of inlining are known (in particular, for recursive calls appearing within
  local functions).
   * If a recursive call could be redirected to the loop header but is not,
     then (A) the external function remains recursive, rather than a non-rec
     wrapper around the recursive loop header, and (B) the recursion consumes
     stack space. Consequence (A) means in turn that inlining will be pushed
     to unnecessarily avoid inlining the not-actually-recursive wrapper.
   * If a nested recursive call is directed to the loop header, even though
     inlining & contification will both fail to eliminate the nested function,
     then the loop header will need a heap allocated closure, even though the
     "proper" choice would result in an allocation-free (top-level) function.

Compiler Details
================

.. toctree::

        closureconversion
        compiled-examples
        coro
        gc
        optimizations
        match-compilation
        recursive-bindings
        c-types

.. include:: closureconversion.rst
.. include:: compiled-examples.rst
.. include:: coro.rst
.. include:: gc.rst
.. include:: optimizations.rst
.. include:: match-compilation.rst
.. include:: recursive-bindings.rst
.. include:: c-types.rst

Stack Allocation
----------------

From an IR perspective, allocating on the stack instead of the heap (mostly)
just involves toggling a flag on an AllocationSource. There's one extra
subtlety: there must also be a GC root pointing to the stack allocation,
and the GC must know to update the stack slot contents without also trying to
copy the slot contents to the newspace.

There are a few choices in how to expose this functionality at the source level
in a safe way. One approach would be to mimic ALGOL, with implicit mutability::

       let x = stackVAR 2; in
         print_i32 x;
         x := 3;
         print_i32 x;
       end

with a typing rule::

                e :: t
       ---------------
       stackVAR e :: t

To support this illusion, expressions of the form ``x := e`` become stores, and
every other use of a stackvar-bound variable is implicitly replaced (after
typechecking) with a load from the backing slot.

The problem with this approach is that a closure ``{ x }`` should not be
rewritten to ``{ load x }``, as there's no check that the closure is only used
when ``x`` is still live. We can account for this with an ad-hoc check, but
that's both ugly and restrictive.

A subtler problem is a poor interaction with lambda-lifting, which removes
variables from a closure's environment if the variable can be provided from
every call site of the closure. Lambda-lifting must become more complicated to
deal with the fact that the value of ``x`` can vary across program points,
unlike all other (immutable) bindings.

A simple alternative would be to leverage the type system a bit::

       let x = stackREF 2; in
         print_i32 (prim stackref-load x);
         prim stackref-assign x 3;
         print_i32 (prim stackref-load x);
       end

with a typing rule::

                e :: t
       ------------------------
       stackREF e :: StackRef t

Now the type system can be given clear rules to enforce safety for
stack-allocated references. Unfortunately, there are two costs:

#. Majorly, the restrictions for safety prevent *any* function from closing
   over a stackref. As a result, it becomes impossible for a function
   implementing a nested loop to close over a stackref from the outer loop.
#. Minorly, we need separate primitives for loads from stackrefs vs heaprefs,
   because they involve separate types, and we wouldn't know which type
   to infer for a metavariable.

Here's an example of real code which would run afoul of the major restriction::

        energy = { bodies : Array Planet =>
          let e = (ref 0.0); in
            arrayEnum bodies { b1 : Planet => i : Int64 =>
              incrByFloat64 e ...;
              arrayEnumFrom bodies (incr64 i) { b2: Planet => jj : Int64 =>
                let dx = ...;
                    dy = ...;
                    dz = ...;
                    distance = ...;
                in
                  decrByFloat64 e ...;
                end
              };
            };
            e^
          end
        };

To turn ``e`` into a stackref, we would need to statically know that it's safe
for the ``arrayEnum`` thunk to close over ``e``, which implies knowing something
about the behavior of ``arrayEnum``.

For reference, here are the definitions from the stdlib::

        arrayEnumFrom = { forall t:Type,
                          a : Array t =>
                          k : Int64 =>
                          f : { t => Int64 => () } =>
          if k <Int64 prim_arrayLength a
            then f a[primitive_trunc_i64_i32 k] k;
                 arrayEnumFrom a (incr64 k) f
            else ()
          end
        };

        arrayEnum = { forall t:Type,
                      a : Array t =>
                      f : { t => Int64 => () } =>
          arrayEnumFrom a (primitive_sext_i64_i32 0) f
        };

and the result of inlining these definitions (not currently performed)::

        energy = { bodies : Array Planet =>
          let e = (ref 0.0); in
            rec arrayEnumFromF = { forall t:Type,   af : Array t =>
                                                    kf : Int64 =>
                                                    ff : { t => Int64 => () } =>
                            if kf <Int64 prim_arrayLength af
                              then ff af[primitive_trunc_i64_i32 kf] kf;
                                   arrayEnumFromF af (incr64 kf) ff
                              else ()
                            end
                          };
             rec arrayEnumFromH = { forall t:Type,  ah : Array t =>
                                                    kh : Int64 =>
                                                    fh : { t => Int64 => () } =>
                            if kh <Int64 prim_arrayLength ah
                              then fh ah[primitive_trunc_i64_i32 kh] kh;
                                   arrayEnumFromH ah (incr64 kh) fh
                              else ()
                            end
                          }; in
            in
            let f = { b1 : Planet => i : Int64 =>
                        incrByFloat64 e ...;
                        let h = { b2: Planet => jj : Int64 =>
                                  let dx = ...; // using b1 and b2
                                      dy = ...;
                                      dz = ...;
                                      distance = ...;
                                  in
                                    decrByFloat64 e ...;
                                  end
                                }; in
                          arrayEnumFromH bodies (incr64 i) h;
                        end
                      };
            in
              arrayEnumFromF bodies (primitive_sext_i64_i32 0) f
              e^
            end
          end
        };

Now that ``arrayEnumFrom`` has been inlined, each instantiation gets passed
a single return continuation (trivially, because they each have a single
external call site and the only internal calls are tail calls). As a result,
the instantiations are both eligible for contification. Another benefit of
inlining is that ``fh`` and ``ff`` both have only one thunk which can flow
to the respective binder. As a result, inlining ``f`` for ``ff`` is a shrinking
reduction::

        energy = { bodies : Array Planet =>
          let  e = (ref 0.0);
          cont arrayEnumFromH = { forall t:Type,  ah : Array t =>
                                                  kh : Int64 =>
                                                  fh : { t => Int64 => () } =>
                          if kh <Int64 prim_arrayLength ah
                            then fh ah[primitive_trunc_i64_i32 kh] kh;
                                 arrayEnumFromH ah (incr64 kh) fh
                            else ()
                          end
                        }; in
          cont arrayEnumFromF = { forall t:Type,   af : Array t =>
                                                  kf : Int64 =>
                          if kf <Int64 prim_arrayLength af
                            then
                              let b1 = af[primitive_trunc_i64_i32 kf];
                                  i  = kf;
                              in
                                incrByFloat64 e ...;
                                let h = { b2: Planet => jj : Int64 =>
                                          let dx = ...; // using b1 and b2
                                              dy = ...;
                                              dz = ...;
                                              distance = ...;
                                          in
                                            decrByFloat64 e ...;
                                          end
                                        }; in
                                  arrayEnumFromH bodies (incr64 i) h;
                                end
                              end;
                              arrayEnumFromF af (incr64 kf)
                            else ()
                          end
                        };
          in
              arrayEnumFromF bodies (primitive_sext_i64_i32 0)
              e^
          end
        };

As it happens, inlining ``h`` is also safe, but in general, safely doing such
inlining requires a proof that the environment of ``h`` at its definition site
is the same as at its call sites. In the general case, given an oracle answering
queries about which functions flow to which call sites, inlining requires
environment analysis (a.k.a. must-alias analysis), as pioneered by Matt Might
and Olin Shivers. However (and fortunately for us!) I believe that data flow
analysis by itself cannot identify flows-to facts which would be unsound without
environment analysis.

Inlining ``h`` yields::

        energy = { bodies : Array Planet =>
          let  e = (ref 0.0);
          cont arrayEnumFromH = { forall t:Type,  ah : Array t =>
                                                  kh : Int64 =>
               if kh <Int64 prim_arrayLength ah
                 then
                   let b2: Planet = ah[primitive_trunc_i64_i32 kh];
                       jj : Int64 = kh;
                   in
                           let dx = ...; // using b1 and b2
                               dy = ...;
                               dz = ...;
                               distance = ...;
                           in
                             decrByFloat64 e ...;
                           end
                   end;
                   arrayEnumFromH ah (incr64 kh) fh
                 else ()
               end
             }; in
          cont arrayEnumFromF = { forall t:Type,   af : Array t =>
                                                   kf : Int64 =>
                if kf <Int64 prim_arrayLength af
                  then
                    let b1 = af[primitive_trunc_i64_i32 kf];
                        i  = kf;
                    in
                      incrByFloat64 e ...;
                      arrayEnumFromH bodies (incr64 i);
                    end;
                    arrayEnumFromF af (incr64 kf)
                  else ()
                end
              };
          in
              arrayEnumFromF bodies (primitive_sext_i64_i32 0)
              e^
          end
        };

Inlining has implicitly eliminated closure allocation and turned the code
into an efficient pair of nested loops, exactly as would be generated by
a primitive looping construct.


Delta-CFA
~~~~~~~~~

http://matt.might.net/papers/might2006dcfa.pdf gives this example of a
hard-to-spot inlining opportunity::

        (\_z (z)
          (letrec ((loop (\_lp (f s)
                 [f s (\_fs (fs) (loop f fs))])))
            (loop (\_o (x k) (k z)) 0)))

rewritten::

        { z =>
          let cz = { x => z };
          rec loop = { f s => loop f (f s) };
          in
            loop cz 0
          end
        }

Simple beta-reduction can't spot this, but it's trivial to recognize
in a data-flow framework like Hoopl.

Another (pathological) example::

       let f = { x h => if x == 0 then h ! else { x } end };
       in f 0 (f 3 0) end

As written, that doesn't satisfy a static type checker. However, we can tweak
the example::

       let f = { x m =>
        case m of
          Nothing => Just { x }
          Just h => h !
        end
       }; in f 0 (f 3 Nothing) end

The code as written evaluates to 3. Now, the only lambda which flows to ``h``
is ``{ x }``, so we might go ahead and inline (and beta-reduce) it::

       let f = { x m =>
        case m of
          Nothing => Just { x }
          Just h => x
        end
       }; in f 0 (f 3 Nothing) end

This is wrong: the result is now 0 instead of 3.  One way of seeing why this
inlining was bogus is that ``{ x }`` escaped from the scope of the binding of
one of its free variables, which introduced the opportunity for it to go wrong.
Consider this very similar example::

       let x = ...;
           f = { z m =>
        case m of
          Nothing => Just { x }
          Just h => h !
        end
       }; in f 0 (f 3 Nothing) end

Now the inlining is a-OK; the difference is that ``{ x }`` never escapes the
scope of ``x``. This view is **more conservative** than delta-CFA: if the
original example ended with ``f 3 (f 3 Nothing)``, delta-CFA would observe that
the inlining were acceptable, because the environments are guaranteed to be
equivalent (up to free variables) at the definition and use points of the
closure. On the other hand, the scope-escaping view would conservatively reject
the possibility of inlining, because the closure **escapes** the scope of ``x``.

.. note::

   In a data-flow framework, "escaping" is even more conservative, and I don't
   think that the environment problem actually occurs in practice without using
   aggressive control-flow analysis, which can reason about where returned/
   escaping values can flow. Consider: in order for a function to escape the
   scope of one of its free variables, the function must escape upwards, but
   return continuations are completely opaque to pure data flow analysis...

.. note::

   Research question: how common is it to encounter call sites with one known
   callee, where the callee may escape the scope of its innermost free variable?

Emscripten
----------

The Emscripten project gets us (maybe)
90% of the way to running Foster in a browser.
The main obstacles remaining:

* The runtime currently dynamically links to ``chromium_base``,
  instead of statically linking it in, mainly for compilation-speed reasons.
  Several possible fixes:

   * link statically against ``chromium_base.bc``
     instead of dynamically against ``chromium_base.so``
   * reduce dependency on chromium_base by re-implementing in C++ or foster
   * create a JS-specific platform analogue to ``chromium_base``.

* Currently emscripten does not support stack switching, which means we can't
  use coroutines. But at least programs which do not use coroutines will still
  work, and there has been some work by others on
  `compiling delimited continuations to JS
  <http://users-cs.au.dk/danvy/sfp12/papers/thivierge-feeley-paper-sfp12.pdf>`_.
* The garbage collector uses a custom backtrace function.
  Maybe emscripten has a port of libunwind?
* An eventual implementation of parallelism would probably need to be adapted
  from a shared-state to the pure message passing capabilities provided by JS.

On the one hand, compiling directly from Foster IR to JS, bypassing LLVM
entirely, would enable support for coroutines and **might** result in faster
code. However, we'd have to do slightly more work to use other libraries
compiled from C++ via emscripten.
