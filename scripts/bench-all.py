#!/usr/bin/env python3

# Copyright (c) 2013 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

from collections import defaultdict

try:
  from scripts.run_cmd import run_cmd, walltime, elapsed
  import fit
except Exception as e:
  print(e)
  print()
  print("You'll probably need to add the foster/ dir to PYTHONPATH.")
  print()
  raise

import os
import sys
import subprocess
import itertools
import datetime
import json
import yaml
import re
import time

import pin_opcodemix

from optparse import OptionParser

script_start = walltime()
datestr = datetime.datetime.now().strftime('%Y-%m-%d@%H.%M.%S')
_scripts_dir = os.path.dirname(sys.argv[0])

# http://code.activestate.com/recipes/52308-the-simple-but-handy-collector-of-a-bunch-of-named/
class Bunch:
    def __init__(self, **kwds):
        self.__dict__.update(kwds)

def mkdir_p(d):
  subprocess.call("mkdir -p %s" % d, shell=True)

def ensure_dir_exists(d):
  mkdir_p(d)

def data_base_dir():
  return 'data'

def data_dir():
  return os.path.join(data_base_dir(), datestr)

def testfrag_to_pathfrag(testfrag):
  return testfrag.replace('/', '__')

def test_data_dir(testfrag, tags):
  return os.path.join(data_dir(), testfrag_to_pathfrag(testfrag), str(tags))

def datapath(testfrag, tags, base):
  return os.path.join(test_data_dir(testfrag, tags), base)

def distribute_tag(pair):
  (tag, vals) = pair
  return [(tag, val) for val in vals]

def format_flag(keyval):
  return "%s=%s" % keyval

def format_flags(tagshortflag):
  (tag, (short, flag)) = tagshortflag
  return (format_flag((tag, short)), flag)

def format_tags(tags_tup):
  return ("[%s]" % ','.join(tags_tup))

def scripts_dir():
  return _scripts_dir

def root_dir():
  return os.path.join(scripts_dir(), '..')

def obj_dir():
  return os.path.join(scripts_dir(), '..', '_obj')

def load(jsonpath):
  with open(jsonpath, 'r') as jsonfile:
    return yaml.safe_load(jsonfile)

kNumIters = 16

def pause_before_test():
  time.sleep(0.060)

def secs_of_ms(ms):
  return float(ms) / 1000.0

# Synopsis: (rv, ms) = shell_out("make some_target")
def shell_out(cmdstr, stdout=None, stderr=None, showcmd=False):
  start = walltime()
  rv = subprocess.call(cmdstr, stdout=stdout, stderr=stderr, shell=True)
  end = walltime()

  if showcmd:
      print("::^^^::", cmdstr)

  return (rv, elapsed(start, end))

def exec_for_testpath(testpath):
    # If testpath is "speed/micro/addtobits",
    # test_name will be "addtobits"
    test_name = os.path.basename(testpath)
    return os.path.join(obj_dir(), "test-tmpdir/%s/%s" % (test_name, test_name))

# testpath might be "speed/micro/addtobits" for example.
def gotest_with(testpath, tags, flagstrs, extra_cmdline_str=''):
  ensure_dir_exists(test_data_dir(testpath, tags))
  compile_txt_path = datapath(testpath, tags, 'compile.txt')
  with open(compile_txt_path, 'w') as outfile:
    cmdstr = ' '.join([os.path.join(scripts_dir(), 'gotest.sh'),
                       testpath,
                       '-I', os.path.join(root_dir(), 'stdlib'),
                       extra_cmdline_str])
    cmdstr += ' '.join([s for s in flagstrs if s])
    #print ": $ " + cmdstr + " &> " + compile_txt_path
    shell_out("rm -f %s" % exec_for_testpath(testpath))
    run_cmd(cmdstr, stdout=outfile, stderr=outfile)
    shell_out("cp %s %s" % (exec_for_testpath(testpath),
                            datapath(testpath, tags, 'exe.exe')))

def intersection_of_sets(sets):
  return set.intersection(*sets)

def union_of_sets(sets):
  return set.union(*sets)

def merge_dicts(x, y):
  z = x.copy()
  z.update(y)
  return z

def zip_dicts(ds):
  """
  Transforms [{k1:v1,...}, {k1:v2,...}, ...]
  into       {k1:[v1,v2,...], ...}
  """
  raw_keys = [set(d.keys()) for d in ds]
  common_keys = intersection_of_sets(raw_keys)
  all_keys    = union_of_sets(raw_keys)
  uncommon_keys = all_keys - common_keys
  if len(uncommon_keys) > 0:
    print("zip_dicts() saw uncommon keys: ", uncommon_keys)
  d = {}
  for k in common_keys:
    d[k] = [e[k] for e in ds]
  return d

def matches(needle, haystack):
  return needle in haystack

def matches_any(subj, needles):
  for needle in needles:
    if matches(needle, subj):
      return True
  return False

def should_test(subj, options):
  return len(options.tests) == 0 or matches_any(subj, options.tests)

def extract_foster_compile_stats(testpath, tags):
  mid_total_ms = None
  all_total_ms = None
  num_lines = None

  with open(datapath(testpath, tags, 'compile.txt'), 'r') as compile_txt_path:
    lines = compile_txt_path.readlines()
    for line in lines:
      m = re.match(r'fpr:.+ fme:\s*(\d+) .+ tot:\s*(\d+)', line)
      if m:
        mid_total_ms = int(m.groups()[0])
        all_total_ms = int(m.groups()[1])
      m = re.match(r'# source lines: (\d+)', line)
      if m:
        num_lines = int(m.groups()[0])

  return  { 'mid_total_ms':mid_total_ms,
            'all_total_ms':all_total_ms,
            'num_lines':num_lines,
            'mid_lines_per_s':float(num_lines) / secs_of_ms(mid_total_ms),
            'all_lines_per_s':float(num_lines) / secs_of_ms(all_total_ms),
          }

def print_timing_line(ms, n, k):
  print("\r>>>> %d ms (%d/%d)" % (ms, n + 1, k), end=' ')
  sys.stdout.flush()

def do_runs_for_gotest(testpath, inputstr, runtimeparams, tags, flagsdict, total, options):
  exec_path = exec_for_testpath(testpath)
  if not os.path.exists(exec_path):
    print("ERROR: compilation failed!")
  else:
    compile_stats = extract_foster_compile_stats(testpath, tags)
    tj = { 'tags'  : tags,
           'flags' : flagsdict,
           'test'  : testpath,
           'input' : inputstr,
           'compile': compile_stats
    }
    stats_seq = []
    os_stats_seq = []
    print(testpath, inputstr, tags)
    print()
    for z in range(total):
      pause_before_test()

      stats_path = datapath(testpath, tags, "stats_%d.json" % z)
      os_stats_path = datapath(testpath, tags, "os_stats_%d.json" % z)
      cmdstr = """time-json --output %s %s %s %s --foster-json-stats "%s" > /dev/null""" \
                 % (os_stats_path, exec_path, inputstr, runtimeparams, stats_path)

      print(": $ " + cmdstr + "         (%d of %d; tags=%s)" % (z + 1, total, tags))

      (rv, ms) = shell_out(cmdstr)
      assert rv == 0
      print_timing_line(ms, z, total)

      stats_seq.append(load(stats_path))
      stats = load(os_stats_path)
      stats['py_run_ms'] = ms
      os_stats_seq.append(stats)

    tj['outputs'] = merge_dicts(zip_dicts(stats_seq), zip_dicts(os_stats_seq))

    if options.pindir is not None:
      opts = Bunch(pindir = options.pindir, outfile = datapath(testpath, tags, 'opcodemix.out'))
      pin_opcodemix.run_pin(opts, [exec_path, inputstr])

    with open(datapath(testpath, tags, 'timings.json'), 'a') as results:
      json.dump(tj, results, indent=2, separators=(',', ':'))
      results.write(",\n")

def compile_and_run_test(testpathfragment, extra_compile_args, inputstr, runtimeparams,
                         tags, flagstrs,  flagsdict, num_iters, options):
  gotest_with(testpathfragment, tags, flagstrs, extra_compile_args)
  do_runs_for_gotest(testpathfragment, inputstr, runtimeparams, tags, flagsdict, num_iters, options)

def flags_of_factors(all_factors):
  return list(itertools.chain(*
           (itertools.product(*map(distribute_tag, factors))
                for factors in all_factors)))

# all_factors :: [ [ (tag, [(symbolic-tag-val, cmd-line-flag)] ) ] ]
def generate_all_combinations(all_factors, num_iters):
  allflags = flags_of_factors(all_factors)
  plan = []
  # For example, flags might be the tuple
  # (('inline',  ('yes', '--me-arg=--inline')),
  #  ('LLVMopt', ('O2',  '--backend-optimize')),
  #  ('donate',  ('yes', '')))
  #
  # Then tags_tup would be ('inline=yes', 'LLVMopt=O2', 'donate=yes')
  # and  flagstrs would be ('--me-arg=--inline', '--backend-optimize', '')
  # and  tags     would be "[inline=yes,LLVMopt=O2,donate=yes]"
  for flags in allflags:
    tags_tup, flagstrs = list(zip(*[format_flags(flgs) for flgs in flags]))
    tags = format_tags(tags_tup)
    flagsdict = {}
    for (tag, (short, arg)) in flags:
      flagsdict[tag] = short
    plan.append( (tags, flagstrs, flagsdict, num_iters) )
  return plan

def plan_fragments(plan, do_compile_and_run):
  fragments = []
  for planinfo in plan:
    def plan_fragment(planx=planinfo):
      (tags, flagstrs, flagsdict, num_iters) = planx
      do_compile_and_run(tags, flagstrs, flagsdict, num_iters)
      print("Elapsed time:", str(datetime.timedelta(milliseconds=elapsed(script_start, walltime()))))
    fragments.append(plan_fragment)
  return fragments

shootout_original_benchmarks = [
  ('third_party/shootout/nbody',         ['nbody.gcc-2.c'],         ['350000']),
  ('third_party/shootout/fannkuchredux', ['fannkuchredux.gcc-1.c'], ['10']),
  ('third_party/shootout/spectralnorm',  ['spectralnorm.gcc-3.c'],  ['850']),
  ('third_party/shootout/mandelbrot',    ['mandel.c'],              ['1024']),
]

other_third_party_benchmarks = [
  ('third_party/siphash',  ['csiphash.c', 'csiphash_driver.c'], ['32', '1000000']),

  ('third_party/shootout/mandelbrot/rust',  ['src/main.rs'],    ['1024']),
  ('third_party/shootout/mandelbrot/sml',               ['mandelbrot.sml'],       ['1024']),
  ('third_party/shootout/mandelbrot/sml/first-order',   ['mandelbrot_fo.sml'],    ['1024']),
  ('third_party/shootout/mandelbrot/sml/higher-order',  ['mandelbrot_ho.sml'],    ['1024']),
  ('third_party/shootout/mandelbrot/ocaml/first-order',   ['mandelbrot_firstorder.ml'],  ['1024']),
  ('third_party/shootout/mandelbrot/ocaml/higher-order',  ['mandelbrot_higherorder.ml'], ['1024']),

  ('third_party/shootout/binarytrees/gcc',  ['binarytrees.c'],    ['14']),
]

shootout_benchmarks = [
   ('speed/micro/addtobits',                               '50000', '', []),

   ('speed/shootout/nbody',                               '350000', '', []),
   ('speed/shootout/nbody-loops',                         '350000', '', []),

   ('speed/shootout/mandelbrot',                          '1024', '', []),

   ('speed/shootout/spectralnorm',                         '850', '', []),

   ('speed/shootout/fannkuchredux',                         '10', '', []),
   ('speed/shootout/fannkuchredux-nogc',                    '10', '', []),
   #('speed/shootout/fannkuchredux-nogc-stackref',           '10', '',  []),
   #('speed/shootout/fannkuchredux-nogc-stackref-unchecked', '10', '',  []),
   ('speed/shootout/fannkuchredux-unchecked',               '10', '',  []),


   ('speed/shootout/binarytrees', '14', """--foster-heap-MB=10""", [('heapsize', [('10M', '')]),
   ]),
]

def benchmark_third_party_code(sourcepath, flagsdict, tags, exe, argstrs,
                               num_iters, options, compile_stats):
  argstr = ' '.join(argstrs)
  tj = { 'tags'  : tags,
         'flags' : flagsdict,
         'test'  : sourcepath,
         'input' : argstr,
        'outputs': {},
        'compile': compile_stats
       }
  os_stats_seq = []
  print(sourcepath, argstr, tags)
  for z in range(num_iters):
    pause_before_test()

    with open(datapath(sourcepath, tags, 'out.txt'), 'w') as out:
      os_stats_path = datapath(sourcepath, tags, "os_stats_%d.json" % z)

      cmdstr = """time-json --output %s %s %s""" \
                 % (os_stats_path, exe, argstr)
      (rv, ms) = shell_out(cmdstr, stderr=out, stdout=out)
      assert rv == 0
      print_timing_line(ms, z, num_iters)

      stats = load(os_stats_path)
      stats['py_run_ms'] = ms
      os_stats_seq.append(stats)
  tj['outputs'] = zip_dicts(os_stats_seq)

  if options.pindir is not None:
    opts = Bunch(pindir = options.pindir, outfile = datapath(sourcepath, tags, 'opcodemix.out'))
    pin_opcodemix.run_pin(opts, [exe, argstr])

  with open(datapath(sourcepath, tags, 'timings.json'), 'a') as results:
    json.dump(tj, results, indent=2, separators=(',', ':'))
    results.write(",\n")

def countlines(path):
  return len(open(path, 'r').readlines())

def benchmark_third_party(third_party_benchmarks, options):
  """
  Input: a list of (benchmark name, input file list, input arguments)
  Returns: a list of lambdas
  """
  nested_plans = []
  for (sourcepath, filenames, argstrs) in third_party_benchmarks:
    if should_test(sourcepath, options):
      all_factors = select_factors(guess_language(filenames[0]))
      planq = generate_all_combinations(all_factors, kNumIters)
      nested_plans.append((sourcepath, filenames, argstrs, planq))

  plan_lambdas = []
  
  for planinfo in nested_plans:
    def compile_and_run_shootout(tags, flagstrs, flagsdict, num_iters, planinfo=planinfo):
      (sourcepath, filenames, argstrs, plann) = planinfo
      sourcedir =  os.path.join(root_dir(), sourcepath)
      filepaths = [os.path.join(sourcedir, filename) for filename in filenames]

      ensure_dir_exists(test_data_dir(sourcepath, tags))
      exe = datapath(sourcepath, tags, "test.exe")
      assert not ' ' in exe

      lang = flagsdict['lang']

      if lang == 'rust':
        shell_out("cp %s %s" % (' '.join(filepaths), datapath(sourcepath, tags, '')))
        (rv, ms) = shell_out("rustc %s %s -o %s" % (' '.join(flagstrs), ' '.join(filepaths), exe))
        benchmark_third_party_code(sourcepath, flagsdict, tags, exe, argstrs,
                                   num_iters, options, {})
        shell_out("rm " + exe)

      if lang == 'ocaml' and False:
        shell_out("cp %s %s" % (' '.join(filepaths), datapath(sourcepath, tags, '')))
        (rv, ms) = shell_out("ocamlopt %s %s -o %s" % (' '.join(flagstrs), ' '.join(filepaths), exe))
        benchmark_third_party_code(sourcepath, flagsdict, tags, exe, argstrs,
                                   num_iters, options, {})
        shell_out("rm " + exe)

      if lang == 'sml' and False:
        mlton = '/home/benkarel/mlton-git/build/bin/mlton'
        tmpfile = "_foster_tmp"
        shell_out("cp %s %s" % (' '.join(filepaths), datapath(sourcepath, tags, '')))
        (rv, ms) = shell_out("%s %s -output %s %s" % (mlton, ' '.join(flagstrs), tmpfile, ' '.join(filepaths)))
        shell_out("mv %s %s" % (tmpfile, exe))
        benchmark_third_party_code(sourcepath, flagsdict, tags, exe, argstrs,
                                   num_iters, options, {})
        shell_out("rm " + exe)

      if lang == 'c':
        # Produce combined source program for preprocessing
        combined_code = datapath(sourcepath, tags, "combined.c")
        preprocessed_code = datapath(sourcepath, tags, "combined.pp.c")
        shell_out("cat %s > %s" % (' '.join(filepaths), combined_code))
        shell_out("gcc -pipe -Wall -Wno-unknown-pragmas -E %s -o %s" % (combined_code, preprocessed_code))
        combined_code_lines = countlines(combined_code)
        preprocessed_code_lines = countlines(preprocessed_code)

        compile_cmd = "gcc -pipe -Wall -Wno-unknown-pragmas %s %s -o %s -lm" % (' '.join(flagstrs), combined_code, exe)
        (rv, ms) = shell_out(compile_cmd)
        compile_stats = {
          'num_source_lines' : combined_code_lines,
          'num_lines'  : preprocessed_code_lines,
          'all_total_ms' : ms,
          'all_lines_per_s' : float(preprocessed_code_lines) / secs_of_ms(ms)
        }

        benchmark_third_party_code(sourcepath, flagsdict, tags, exe, argstrs,
                                  num_iters, options, compile_stats)
        shell_out("rm " + exe)

    plan_lambdas.extend(plan_fragments(planinfo[3], compile_and_run_shootout))
  return plan_lambdas

# --be-arg=--gc-track-alloc-sites
# --be-arg=--dont-kill-dead-slots
# --optc-arg=-O0
# --optc-arg=-O2
# --optc-arg=-Onone
# --optc-arg=-no-specialize-memallocs
# --optc-arg=-foster-insert-timing-checks

#  ('abc', [('safe',    ''),
#           ('unsafe' , '--be-arg=-unsafe-disable-array-bounds-checks')]),
#
# ('inline', [('yes', '--me-arg=--inline'),
#             ('no' , '--me-arg=--no-inline')
#            ]),
# ('LLVMopt', [('O2', '--backend-optimize')
#             ,('O0', '')
#             ]),
# ('donate', [('yes', ''),
#             ('no' , '--me-arg=--no-donate')
#            ]),
#('inlineSize', [(str(x), '--me-arg=--inline-size-limit=%d' % x) for x in range(0, 101)])

def addfactors(factors, newfactors):
  return [factor + newfactors for factor in factors]

foster_factors = addfactors([
 [ # full optimization, showing limits of array bounds checking
   ('inline', [('yes', '--me-arg=--inline'), ]),
   ('LLVMopt', [('O2', '--backend-optimize')]),
   ('abc', [('unsafe' , '--be-arg=-unsafe-disable-array-bounds-checks')]),
   ('donate', [('yes', '')]),
   ('gc', [('nonmoving', '--me-arg=--non-moving-gc')]),
 ],
 [ # full optimization, retaining safety
   ('inline', [('yes', '--me-arg=--inline'), ]),
   ('LLVMopt', [('O2', '--backend-optimize')]),
   ('abc', [('safe' , '')]),
   ('donate', [('yes', '')]),
   ('gc', [('default', '')]),
 ],
 [
   ('inline', [ ('no' , '--me-arg=--no-inline') ]),
   ('LLVMopt', [('O0', '')]),
   ('abc', [('safe' , '')]),
   ('donate', [('yes', ''),]),
   ('gc', [('default', '')]),
 ]
], [('lang', [('foster', '')]),
    ('date', [(datestr, '')]),
   ])

clang_factors = [factor + [('lang', [('c', '')]),
                           ('date', [(datestr, '')]),
                          ] for factor in [
  [
    ('LLVMopt', [('O3', '-O3')]),
    ('sse',     [('yes', '-march=native -mfpmath=sse')]),
  ],
  [
    ('LLVMopt', [('O2', '-O2'),
                  ('O0', '-O0')]),
    ('sse',     [('no', '')]),
  ],
]]

ocaml_factors = [factor + [('lang', [('ocaml', '')]),
                           ('date', [(datestr, '')]),
                        ] for factor in [
 [ ('opt', [('O2', '-O2'),
            ('O3', '-O3'),
            ('default', '') ]),
   ('safe', [('yes', ''), ]),
 ],
 [ # unboxed?
   ('opt', [('O3', '-O3'), ]),
   ('safe', [('no', '-unsafe -fno-PIC'), ]),
 ],
]]

mlton_factors = [factor + [('lang', [('sml', '')]),
                           ('date', [(datestr, '')]),
                        ] for factor in [
 [ ('codegen', [('llvm', '-codegen llvm'),
                ('c',    '-codegen c'),
                ('amd64','-codegen amd64'), ]),
   ('safe', [('yes', ''), ]),
 ],
]]

rust_factors = [factor + [('lang', [('rust', '')]),
                          ('date', [(datestr, '')]),
                         ] for factor in [
  [
    ('LLVMopt', [('O3', '-C opt-level=3'),
                 ('O2', '-C opt-level=2')]),
    ('cpu',     [('native', '-C target-cpu=native')]),
  ],
]]

def guess_language(filename):
  if filename[-3:] == ".rs":
    return "rust"
  if filename[-3:] == ".ml":
    return "ocaml"
  if filename[-4:] == ".sml":
    return "sml"
  return "c"

def select_factors(lang):
  if lang == "c":
    return clang_factors
  if lang == "ocaml":
    return ocaml_factors
  if lang == "rust":
    return rust_factors
  if lang == "sml":
    return mlton_factors
  raise Exception("Unknown language: " + lang)

def benchmark_shootout_programs(options, num_iters=kNumIters):
  plan_lambdas = []
  for benchinfo in shootout_benchmarks:
    if should_test(benchinfo[0], options):
      def compile_and_run(tags, flagstrs, flagsdict, num_iters, benchi=benchinfo):
        (testfrag, argstr, runtimeparams, bench_factors) = benchi
        compile_and_run_test(testfrag, '', argstr, runtimeparams,
                            tags, flagstrs, flagsdict, num_iters, options)
      print(benchinfo)
      plan = generate_all_combinations(addfactors(foster_factors, benchinfo[3]), kNumIters)

      plan_lambdas.extend(plan_fragments(plan, compile_and_run))
  return plan_lambdas

def collect_all_timings():
  alltimings = os.path.join(data_dir(), 'all_timings.json')
  shell_out("echo [ > %s" % alltimings)
  shell_out("find %s -name 'timings.json' | xargs cat >> %s" % (data_dir(), alltimings))
  shell_out("echo ] >> %s" % alltimings)
  print(alltimings)

def fixup_pindir(options):
  if options.pindir is None:
    for path in [ os.path.join(os.path.expanduser('~'), 'sw', 'local', 'pin') ]:
      if os.path.exists(path):
        options.pindir = path
        return True
  return False

def get_test_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--test", action="append", dest="tests", default=[],
                    help="Consider only these tests by (substring of) name.")
  parser.add_option("--comment", action="append", dest="comments", default=[],
                    help="Associate a comment with this run.")
  parser.add_option("--pindir", dest="pindir", action="store", default=None,
                    help="Path to the `pin` root, if available.")
  parser.add_option("--no-randomized-order", dest="randomized_order", action="store_false", default=True,
                    help="Disable running tests in a randomized order")
  return parser

def main():
  parser = get_test_parser("""usage: %prog [options]\n""")
  (options, args) = parser.parse_args()

  fixup_pindir(options)

  start = datetime.datetime.utcnow()
  ensure_dir_exists(data_dir())
  plan = []
  plan.extend( benchmark_third_party(other_third_party_benchmarks, options) )
  plan.extend( benchmark_third_party(shootout_original_benchmarks, options) )
  plan.extend( benchmark_shootout_programs(options)                         )

  if options.randomized_order:
    import random
    print("randomizing test order...")
    random.shuffle(plan)

  print("Plan has", len(plan), "items...")
  for (n,f) in enumerate(plan):
    print("[%d of %d]" % (n + 1, len(plan)))
    f()

  collect_all_timings()
  end = datetime.datetime.utcnow()
  print("Total elapsed time:", end - start)

if __name__ == '__main__':
  main()

# To consider separate combinations of factors, we can do something like:
#    for num_factors_to_use in range(1, len(factors) + 1):
#      combos = list(itertools.combinations(factors, num_factors_to_use))
# For example, itertools.combinations(list('abcd'), 2)
# is  [('a', 'b'), ('a', 'c'), ('a', 'd'), ('b', 'c'), ('b', 'd'), ('c', 'd')]
