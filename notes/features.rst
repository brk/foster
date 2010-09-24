Motivation for Features
=======================

LLVM Lowerings
--------------

LLVM enforces a distinction between objects, which live in memory
and can be mutated via ``store`` instructions,
and values, which are single-assignment (i.e. not mutable)
and live in registers.

LLVM provides a highly effective optimization pass called ``mem2reg``,
which takes values stored on the stack (in memory) and promotes them
to registers. The ``mem2reg`` pass is used for all function-local variables
in llvm-gcc and clang.

There are three different ways in which a source-level variable
could be lowered to LLVM IR, which correspond to different semantics
for the variable. Possible representations for a variable of type
i32, which generalizes to any type T:

=======  ==========   =========  ==============================

Used As  Stack Slot   Passed As  Comments

=======  ==========   =========  ==============================
i32      N/A          i32        SSA immutable val
i32      i32*         i32        locally-mutable vars
i32      i32**        i32*       C++-style non-const reference
=======  ==========   =========  ==============================

Other combinations are possible, but those are the most
obviously useful. A few items of note:


* The clang frontend emits only the locally-mutable var
  and non-const reference lowerings. The first row of the table
  is handled by ``mem2reg``.

* Java semantics (pass reference by value) can be handled
  entirely by locally-mutable vars.

* C# or C++-style reference semantics could be implemented using
  the third technique; it remains to be seen whether
  reference semantics are actually needed or not.

.. note::

  The simplest approach for now is to use Java semantics
  and have variables of type T live in stack slots of type T*.
  Since most variables will refer to (lowered) pointer types,
  the net effect is to have a type U map to a L(U)* stored
  in a stack slot of type L(U)**.

Unboxing
--------

Coroutines
----------

Impredicative Polymorphism
--------------------------

Overloading
-----------

Effects
-------

Regions
-------

Types
-----

Dependent Types
---------------

ADTs
----

Records
-------

Named Parameters
----------------


.. An interactive code sample::
.. 
..   >>> 1 + 1
..   2
.. 
.. A non-interactive code sample:
.. 
.. .. code-block:: haskell
.. 
..   Y f = f (Y f)
.. 
.. A shell example:
.. 
.. .. code-block:: bash
.. 
..   $ ccmake ../foster
.. 
.. Cool, eh?
.. 
.. Built |today|.
