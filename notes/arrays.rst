Arrays
======

TODO: fancy DML-style dependent types for array indexing.

Primitive Operations
--------------------

Having an interepeted implementation has been useful to keep the language design
"honest" about the semantics, avoiding puns particular to a single implementation.

For example, the interpreter is very clear that (to be updateable) array slots
must be store locations. The question then is: does array subscripting produce
an explicit location, modifiable via the standard assignment primitive, or do
the operations render the store location implicit?

Here the LLVM side has an answer: the correct choice is implicit.
The primary reason is that such a pointer is, at the GC level, a derived pointer.
Avoiding casual creation of derived pointers is an obvious design choice.
Furthermore, having explicit separate operations for reading and writing
array slots also provides a nice hook for separate read and write barriers.
Finally, it saves a "superfluous" deref at the source level for array reads.

Types
-----

Musings::

  Array n T ::              Type
  Array n ::      { Type -> Type }
  Array :: { Nat -> Type -> Type }

  Array :: { {n:Int | n > 0} -> Type -> Type }


  DArray :: { Type -> Type }
  $DArray T ::       Type


  newArray :: { (a:Type) -> (n:Nat) -> {Nat -> a} -> Array n a }
  newDArray :: { (a:Type) -> Int -> {Int -> a} -> DArray a }
