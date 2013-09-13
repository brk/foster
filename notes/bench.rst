Benchmarking Infrastructure
===========================

The benchmark infrastructure separates the tasks of
collecting and analyzing/visualizing benchmark data.

The ``bench-all.py`` script will run a set of benchmark programs under some number
of compile-time and run-time configurations, recording relevant statistics to the file system.

For a compilation of ``speed/micro/addtobits``
with the flags ``inline=no`, `LLVMopt=O0``, and ``donate=no``:
* ``data/2013-05-28@09.48.52/speed__micro__addtobits/[inline=no,LLVMopt=O0,donate=no]/compile.txt``
* ``data/2013-05-28@09.48.52/speed__micro__addtobits/[inline=no,LLVMopt=O0,donate=no]/exe.exe``
* ``data/2013-05-28@09.48.52/speed__micro__addtobits/[inline=no,LLVMopt=O0,donate=no]/stats_0.json``
* ``data/2013-05-28@09.48.52/speed__micro__addtobits/[inline=no,LLVMopt=O0,donate=no]/stats_n.json``
* ``data/2013-05-28@09.48.52/speed__micro__addtobits/[inline=no,LLVMopt=O0,donate=no]/timings.json``
* ``data/2013-05-28@09.48.52/all_timings.json``

timings.json
------------

The format of the ``timings.json`` file would be, for example::

    {
      "test":"speed/micro/addtobits",
      "input":"50000",
      "flags":{
        "inline":"yes",
        "donate":"no",
        "LLVMopt":"O2"
      },
      "py_run_ms":[ 353, 352, ...  352 ],
      "tags":"[inline=yes,LLVMopt=O2,donate=no]"
    },

stats_n.json
------------

The format of the ``stats_n.json`` file varies with compile-time options. One example::
    {
    'Elapsed_runtime_s' :  0.347,
    'Elapsed_runtime_ms': 347.801,
    'Initlzn_runtime_s' :  0.003,
    'Initlzn_runtime_ms':  3.435,
    '     GC_runtime_s' :  0.054,
    '     GC_runtime_ms': 54.010,
    'Mutator_runtime_s' :  0.290,
    'Mutator_runtime_ms': 290.356,
    'num_collections' : 500,
    'alloc_num_bytes_gt' : 5.24e+08,
    'semispace_size_kb' : 1024,
    },

Overview
--------

Conceptually, we want to take a list of (input, output) dictionaries,
and produce a list of structured organized views of the provided data.
The input dictionaries might have key/value entries for ``test``, ``input``,
individual flags like ``donate``, and collective values like ``tags``. There
would also probably be an entry for ``revision`` and/or ``date_taken``.
An ``impl_lang`` key would also be helpful.

There are also a few different ways we can slice and dice the input for visualizations:
 * For each individual test, compare the effects of different flags.
 * For each individual test, compare performance across different times/revisions
   at the same flags.
 * Compare output metrics as input size varies (for one or more benchmark impls)
 * Do the same for groups of tests (i.e. different implementations of the same benchmark)
   with a common scale for comparison.
  * Group tests by implementation language

For comparing flag effects across tests, we want::
    [ {
      xlabel:"...",
      results: [
        {legend_text:"...",
          output_samples: [...]
        } ] } ]
Each distinct xlabel would be mapped to an arbitrary (hidden) x-value.

Besides detailed visualizations, it would also be nice to have a compact, easy-to-digest
summary of the overall status of selected implementations against each other:
a table with results (perhaps small inline bar graphs) saying "A is X% faster than B" etc.


