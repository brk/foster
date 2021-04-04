Lexer/Parser Tooling
====================

``tools/tokendump-antlr`` prints a list of tokens in a given Foster source file.
There's a target to build it in the root ``CMakeLists.txt`` file.

``fosterparse`` emits CBOR, which can be pretty-printed like so::

  $ fosterparse -I ../stdlib y.foster y.f.cbor
  $ python3 -m cbor2.tool y.f.cbor
  [["y.foster", "7dd30bc2dd0c971511d51a6c40ada542",
   [63, "MODULE", [0, 72, 0, 72],
    ...
    ["COMMENT", 44, 31, "// (1 << DOUBLE_EXPONENT_BITS) - 1;"],
    ["NEWLINE", 44, 66], ["NEWLINE", 45, 0], ["NEWLINE", 46, 27]]]]
