  $ cd $TMPDIR
  $ fosterc ~/foster/test/syntax-errors/dup-arg-names/dup-arg-names.foster --show-cmdlines -q 2>&1 | ansifilter.py | sed '/me: compilation failed/q'
  Typecheck error: 
  Error when checking foo: had duplicated bindings: ["x"]
  foo = { x:Int32 => x:Int32 => x };
        ~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  
  Unable to type check input module:
  not all functions type checked in SCC: ["foo"]
  me: compilation failed


--------
For context, here's the error one gets from Rust:

error[E0415]: identifier `x` is bound more than once in this parameter list
 --> dan.rust:1:17
. |
1 | fn foo(x : i32, x : i32) -> i32 {
. |
error: aborting due to previous error

For more information about this error, try `rustc --explain E0415`.
--------

Go is much more parsimonious:

./prog.go:7:17: duplicate argument x
---------

Elm:

-- NAME CLASH -------------------------------------------------- Jump To Problem

The `foo` function has multiple `x` arguments.

7| foo x x = x + x
.      ^ ^
How can I know which one you want? Rename one of them!
--------










  $ fosterc ~/foster/test/syntax-errors/incomplete-let/incomplete-let.foster --show-cmdlines -q 2>&1 | ansifilter.py | sed '/Failed to run:/q'
  /home/ben/foster/test/syntax-errors/incomplete-let/incomplete-let.foster:generic error: Unexpected token near the end of line 1:
  
     1: let c =
              ^
  
  <unknown source file>: error: Encountered 1 parsing errors; exiting. (with AST)
  tok : let; tokenNames: <invalid>
  Failed to run:






  $ fosterc ~/foster/test/syntax-errors/dup-func-names/dup-func-names.foster --show-cmdlines -q 2>&1 | ansifilter.py | sed '/me: compilation failed/q'
  Unable to type check input module:
  Unable to check module due to duplicate bindings: 
  
  1:      foo = { 0 };
               ~~~~~
  
  
  3:      foo = { 1 };
                ~~~~~
  
  me: compilation failed
