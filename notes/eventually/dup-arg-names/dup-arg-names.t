  $ cd $TMPDIR
  $ fosterc $INPUT --show-cmdlines -q 2>&1 | ansifilter.py | sed '/me: compilation failed/q'
  Typecheck error: 
  Error when checking foo: had duplicated bindings: ["x"]
  foo = { x:Int32 => x:Int32 => x };
        ~~~~~~~~~~~~~~~~~~~~~~~~~~~
  
  
  Unable to type check input module:
  not all functions type checked in SCC: ["foo"]
  me: compilation failed
