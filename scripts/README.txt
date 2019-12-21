These are quick-and-dirty helper scripts to compile and run foster programs.
You'll probably want to add the scripts/ directory (containing this file)
to your $PATH.

gotest.sh
---------

    $ ./gotest.sh bootstrap/app/mumurhash2
will (using `test.sh`) compile and run the file
    foster/test/bootstrap/app/murmurhash2/murmurhash2.foster

countlines.sh
-------------

Intended to be run from the root checkout.
Reports a coarse breakdown of how big various parts of the compiler and
runtime are in terms of lines of code (counted by `cloc`).

Example output::
    $ countlines.sh
    notes            5588

    compiler/*.cpp   877
    compiler/passes  3405
    compiler/parse   2765
    compiler/base    1377
    compiler/llvm    991
    compiler/me      9694

    runtime          1539
    compiler         19179
    third_party      73823

emcc-foster
-----------

A wrapper around the Emscripten tool ``emcc``, which automatically links in
the standard library bitcode.

list_all.py
-----------

    $ python scripts/list_all.py test/bootstrap
    /home/benkarel/foster/test/bootstrap/inference/tuple-metatyvar/tuple-metatyvar.foster
    /home/benkarel/foster/test/bootstrap/inference/inferred-lambdas/inferred-lambdas.foster
    ...
    /home/benkarel/foster/test/bootstrap/closureconversion/hof-trivial/hof-trivial.foster

Pin-related scripts
-------------------

Look at ``pin-example.sh``  to see how to use Pin to analyse a generated
Foster binary.

``compare-opcodemix.py`` should be used to compare generated optcodemix.out
files from the ``opcodemix`` pintool.

Internal utilities
------------------

* run_test.py
* run_cmd.py
* run_antlr.py
* gtest_wrapper.py
* silent
* stathat.py

watch.py
--------

Mainly used by ``notes/autobuild.sh`` to rebuild the documentation as it is being edited.

Synopsis: $ watch <paths...> - <commands...>

TODO
----

* fit.py
* install-llvm.sh
* parse_args.py -- Just an example code snippet, not a real tool.
