Compiler Overview
==================

The compiler was originally a monolithic C++ binary.
It is now a separate front-end, middle-end, and back-end,
which communicate via protocol buffers.

The front-end is written in C++, and uses ANTLR and LLVM
to turn text strings into parse trees, which it then
massages into AST nodes.

.. note::
    If we ever allow modules to export precedence or other
    syntax rules, then constructing a properly structured
    AST requires being able to get information that depends
    on the contents of other modules.
    The minimal information needed is syntax exports and
    module dependencies.
    In practice, it will also mean that parsing requires
    searching input paths to find module information.

The middle-end is written in Haskell. It takes a module's
AST node and performs resolution (with hardcoded types for
standard library functions) and type checking. Eventually,
type checking should be performed on SCCs of modules.

The back-end is written in C++. The primary advantage of
using C++ rather than Haskell for lowering to LLVM is that
we can use custom LLVM IR passes, as well as our GC plugin.
Right now the ASTs passed out of the front-end and into the
back-end are the same, but that should probably change...

.. ::
    #. Resolution: compute fully-qualified versions of all names.
            At this stage we need to have export information from imported modules.
            This is where we need to build the symbol table.
    #. Typechecking / type inference.
        At the end of this pass, we can emit a module interface AST
        in protobuf format, which can be used directly (in place of
        re-parsing from a string) by other modules importing this module.
    #. Closure Conversion
    #. Code Generation

.. ::
	Module.Submodule.function
	object.subobject.field
	object.subobject.function
	Type.anything?

-------

Module dependency tracking could be done by either the
front-end, middle-end, or driver.
It requires a list of input paths to search.

If parsing is responsible for
collecting and recursively parsing imported modules, then the output is a list
of ``(Either (Protobuf SugaryAST) (Protobuf TypecheckedAST)`` depending on
whether the imported module has been compiled more recently than it was
modified, and the protobufs in either case should embed each module's full
dependency graph. Otherwise, parsing has a much simpler signature
(``String -> Protobuf SugaryAST``), protobufs need only include direct import
information, and sema is responsible for recursively ensuring that all imported
modules are parsed, and for building the import graph from ASTs to determine
the set of recursively imported modules.

.. ::
    Conceptually, though, there are three nominally independent pieces:

    #. Parsing :: ``(String , [InputPath]) -> [Protobuf SugaryAST]``
    #. Type checking :: ``[Protobuf SugaryAST] -> Either (Protobuf TypecheckedAST) (Protobuf CFG , [ImportedModules])``
    #. Code Generation :: ``(Protobuf CFG, [ImportedModules]) -> LLVM IR Module``



Parse Trees
-----------

In order to capture more detailed source token information,
we insert a filter in the ANTLR parser object before starting a
top-level parse. The filter associates token boundaries with ANTLR
parse tree objects. Unfortunately the assocation must be done in a
statically-accessible map. Therefore parsing must be done in a dedicated
parsing context.

A parse tree is a simple tree-encoded representation of an input string.
Parse trees themselves do not have proper semantics: for example, binary
operators corresond in structure to their source ordering, not their
relative precedences.

AST Building
------------

AST building performs an operator precedence post-processing pass to
determine the proper structure of operators.

Currently modules are restricted to topologically sorted imports.
Diatchki, Jones, and Hallgren present a fairly straightforward approach
for handling SCCs of mutually-recursive modules via fixed-point computation
of exports: http://ogi.altocumulus.org/~hallgren/hsmod/Description.pdf
In this case, rather than compiling one module at a time, the compiler
would process one SCC at a time.

