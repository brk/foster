#!/usr/bin/env python

# Copyright (c) 2013 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

from collections import defaultdict

try:
  from scripts.run_cmd import run_cmd, walltime, elapsed
  import fit
except Exception, e:
  print e
  print
  print "You'll probably need to add the foster/ dir to PYTHONPATH."
  print
  raise

import os
import sys
import subprocess
import itertools
import datetime
import json
import yaml

def mkdir_p(d):
  subprocess.call("mkdir -p %s" % d, shell=True)

datestr = datetime.datetime.now().strftime('%Y-%m-%d@%H.%M.%S')
_scripts_dir = os.path.dirname(sys.argv[0])

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

def distribute_tag((tag, vals)):
  return [(tag, val) for val in vals]

def format_flag(keyval):
  return "%s=%s" % keyval

def format_flags((tag, (short, flag))):
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

kNumIters = 10


# Synopsis: (rv, ms) = shell_out("make some_target")
def shell_out(cmdstr, stdout=None, stderr=None, showcmd=False):
  start = walltime()
  rv = subprocess.call(cmdstr, stdout=stdout, stderr=stderr, shell=True)
  end = walltime()

  if showcmd:
      print "::^^^::", cmdstr

  return (rv, elapsed(start, end))

def exec_for_testpath(testpath):
    # If testpath is "speed/micro/addtobits",
    # test_name will be "addtobits"
    test_name = os.path.basename(testpath)
    return os.path.join(obj_dir(), "test-tmpdir/%s/a.out" % test_name)

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
    print ": $ " + cmdstr + " &> " + compile_txt_path
    shell_out("rm -f %s" % exec_for_testpath(testpath))
    run_cmd(cmdstr, stdout=outfile, stderr=outfile)
    shell_out("cp %s %s" % (exec_for_testpath(testpath),
                            datapath(testpath, tags, 'exe.exe')))

def intersection_of_sets(sets):
  return set.intersection(*sets)

def union_of_sets(sets):
  return set.union(*sets)

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
    print "zip_dicts() saw uncommon keys: ", uncommon_keys
  d = {}
  for k in common_keys:
    d[k] = [e[k] for e in ds]
  return d

def do_runs_for_gotest(testpath, inputstr, tags, flagsdict, total):
  exec_path = exec_for_testpath(testpath)
  if not os.path.exists(exec_path):
    print "ERROR: compilation failed!"
  else:
    tj = { 'tags'  : tags,
           'flags' : flagsdict,
           'test'  : testpath,
           'input' : inputstr, }
    stats_seq = []
    for z in range(total):
      stats_path = datapath(testpath, tags, "stats_%d.json" % z)
      os_stats_path = datapath(testpath, tags, "os_stats_%d.json" % z)
      cmdstr = """time-json --output %s %s %s -foster-runtime '{ "dump_json_stats_path" : "%s" }'  > /dev/null""" \
                 % (os_stats_path, exec_path, inputstr, stats_path)
      #print ": $ " + cmdstr + " (%d of %d; tags=%s)" % (z + 1, total, tags)
      (rv, ms) = shell_out(cmdstr)
      print testpath, inputstr, tags, ">>>> ", ms, "ms"
      stats = load(stats_path)
      stats['py_run_ms'] = ms
      stats_seq.append(stats)
    tj['outputs'] = zip_dicts(stats_seq)
    with open(datapath(testpath, tags, 'timings.json'), 'a') as results:
      json.dump(tj, results, indent=2, separators=(',', ':'))
      results.write(",\n")

def compile_and_run_test(testpathfragment, extra_compile_args, inputstr,
                         tags, flagstrs,  flagsdict, num_iters):
  gotest_with(testpathfragment, tags, flagstrs, extra_compile_args)
  do_runs_for_gotest(testpathfragment, inputstr, tags, flagsdict, num_iters)

def flags_of_factors(all_factors):
  return list(itertools.chain(*
           (itertools.product(*itertools.imap(distribute_tag, factors))
                for factors in all_factors)))

# all_factors :: [ [ (tag, [(symbolic-tag-val, cmd-line-flag)] ) ] ]
def generate_all_combinations(all_factors, num_iters):
  allflags = flags_of_factors(all_factors)
  plan = []
  # For example, flags might be the tuple
  # (('inline',  ('yes', '--me-arg=--inline')),
  #  ('LLVMopt', ('O2',  '--optimize=O2')),
  #  ('donate',  ('yes', '')))
  #
  # Then tags_tup would be ('inline=yes', 'LLVMopt=O2', 'donate=yes')
  # and  flagstrs would be ('--me-arg=--inline', '--optimize=O2', '')
  # and  tags     would be "[inline=yes,LLVMopt=O2,donate=yes]"
  for flags in allflags:
    tags_tup, flagstrs = zip(*[format_flags(flgs) for flgs in flags])
    tags = format_tags(tags_tup)
    flagsdict = {}
    for (tag, (short, arg)) in flags:
      flagsdict[tag] = short
    plan.append( (tags, flagstrs, flagsdict, num_iters) )
  return plan

def execute_plan(plan, do_compile_and_run, step_counter, total_steps):
  for (tags, flagstrs, flagsdict, num_iters) in plan:
    start = walltime()
    do_compile_and_run(tags, flagstrs, flagsdict, num_iters)
    end = walltime()
    ms = elapsed(start, end)
    d = datetime.timedelta(milliseconds=ms)
    r = datetime.timedelta(milliseconds=ms * (total_steps - step_counter[0] - 1))
    step_counter[0] += 1
    print "Step %d of %d overall plan took %s, estimated time left: %s..." % (step_counter[0], total_steps, str(d), str(r))

shootout_original_benchmarks = [
  ('third_party/shootout/nbody',         ['nbody.gcc-2.c'],         ['350000']),
  ('third_party/shootout/fannkuchredux', ['fannkuchredux.gcc-1.c'], ['10']),
  ('third_party/shootout/spectralnorm',  ['spectralnorm.gcc-3.c'],  ['850']),
]

other_third_party_benchmarks = [
  ('third_party/siphash',  ['csiphash.c', 'csiphash_driver.c'], ['32', '1000000']),
]

shootout_benchmarks = [
   ('speed/micro/addtobits', '50000'),

   ('speed/shootout/nbody',                               '350000'),
   ('speed/shootout/nbody-loops',                         '350000'),
   ('speed/shootout/nbody-loops-inlined',                 '350000'),
   ('speed/shootout/nbody-loops-mallocs',                 '350000'),
   ('speed/shootout/nbody-loops-unsafe',                  '350000'),
   ('speed/shootout/nbody-loops-unchecked',               '350000'),
   ('speed/shootout/nbody-cont-manually-inlined',         '350000'),
   ('speed/shootout/nbody-cont-manually-inlined-mallocs', '350000'),

   ('speed/shootout/spectralnorm', '850'),

   ('speed/shootout/fannkuchredux',                         '10'),
   ('speed/shootout/fannkuchredux-nogc',                    '10'),
   ('speed/shootout/fannkuchredux-nogc-stackref',           '10'),
   ('speed/shootout/fannkuchredux-nogc-stackref-unchecked', '10'),
   ('speed/shootout/fannkuchredux-unchecked',               '10'),
]

def benchmark_third_party_code(sourcepath, flagsdict, tags, exe, argstrs, num_iters):
  ensure_dir_exists(test_data_dir(sourcepath, tags))
  argstr = ' '.join(argstrs)
  tj = { 'tags'  : tags,
         'flags' : flagsdict,
         'test'  : sourcepath,
         'input' : argstr,
        'outputs': {},
       }
  timings_ms = []
  for z in range(num_iters):
    with open(datapath(sourcepath, tags, 'out.txt'), 'w') as out:
      (rv, ms) = shell_out(' '.join([exe] + argstrs), stderr=out, stdout=out)
      assert rv == 0
      print sourcepath, exe, argstr, ">>>> ", ms, "ms"
      timings_ms.append(ms)
  tj['outputs']['py_run_ms'] = timings_ms

  with open(datapath(sourcepath, tags, 'timings.json'), 'a') as results:
    json.dump(tj, results, indent=2, separators=(',', ':'))
    results.write(",\n")

def benchmark_third_party(third_party_benchmarks):
  nested_plans = []
  for (sourcepath, filenames, argstrs) in third_party_benchmarks:
    all_factors = [factor + [('lang', [('other', '')]),
                             ('date', [(datestr, '')]),
                            ] for factor in [
      [
        ('LLVMopt', [('O3', '-O3')]),
        ('sse',     [('yes', '-march=core2 -mfpmath=sse -msse3 -falign-labels=8')]),
      ],
      [
        ('LLVMopt', [('O2', '-O2'),
                     ('O0', '-O0')]),
        ('sse',     [('no', '')]),
      ],
    ]]
    plan = generate_all_combinations(all_factors, kNumIters)
    nested_plans.append((sourcepath, filenames, argstrs, plan))

  total_steps = sum(len(plan) for (s,f,a, plan) in nested_plans)
  step_counter = [0]

  for (sourcepath, filenames, argstrs, plan) in nested_plans:
    d  =  os.path.join(root_dir(), sourcepath)
    cs = [os.path.join(d, filename) for filename in filenames]
    def compile_and_run_shootout(tags, flagstrs, flagsdict, num_iters):
      exe = 'test_' + tags + ".exe"
      shell_out("gcc -pipe -Wall -Wno-unknown-pragmas %s %s -o %s -lm" % (' '.join(flagstrs), ' '.join(cs), exe), showcmd=True)
      benchmark_third_party_code(sourcepath, flagsdict, tags,
                                  exe, argstrs, num_iters)
    execute_plan(plan, compile_and_run_shootout, step_counter, total_steps)
    shell_out("rm test_*.exe")


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
# ('LLVMopt', [('O2', '--optimize=O2')
#             ,('O0', '--optimize=O0')
#             ]),
# ('donate', [('yes', ''),
#             ('no' , '--me-arg=--no-donate')
#            ]),
#('inlineSize', [(str(x), '--me-arg=--inline-size-limit=%d' % x) for x in range(0, 101)])

all_factors = [factor + [('lang', [('foster', '')]),
                         ('date', [(datestr, '')]),
                        ] for factor in [
 [ # full optimization, showing limits of array bounds checking
   ('inline', [('yes', '--me-arg=--inline'), ]),
   ('LLVMopt', [('O2', '--optimize=O2')]),
   ('abc', [('unsafe' , '--be-arg=-unsafe-disable-array-bounds-checks')]),
   ('donate', [('yes', '')]),
 ],
 [ # full optimization, retaining safety
   ('inline', [('yes', '--me-arg=--inline'), ]),
   ('LLVMopt', [('O2', '--optimize=O2')]),
   ('abc', [('safe' , '')]),
   ('donate', [('yes', '')]),
 ],
 [
   ('inline', [ ('no' , '--me-arg=--no-inline') ]),
   ('LLVMopt', [('O0', '--optimize=O0')]),
   ('abc', [('safe' , '')]),
   ('donate', [('yes', ''),]),
 ]
]]


def benchmark_shootout_programs(num_iters=kNumIters):
  for (testfrag, argstr) in shootout_benchmarks:
    def compile_and_run(tags, flagstrs, flagsdict, num_iters):
      compile_and_run_test(testfrag, '', argstr,
                           tags, flagstrs, flagsdict, num_iters)
    plan = generate_all_combinations(all_factors, kNumIters)
    total_steps = len(plan)
    step_counter = [0]
    execute_plan(plan, compile_and_run, step_counter, total_steps)

def collect_all_timings():
  alltimings = os.path.join(data_dir(), 'all_timings.json')
  shell_out("echo [ > %s" % alltimings)
  shell_out("find %s -name 'timings.json' | xargs cat >> %s" % (data_dir(), alltimings))
  shell_out("echo ] >> %s" % alltimings)
  print alltimings


def main():
  ensure_dir_exists(data_dir())
  benchmark_third_party(other_third_party_benchmarks)
  benchmark_third_party(shootout_original_benchmarks)
  benchmark_shootout_programs()
  collect_all_timings()

if __name__ == '__main__':
  main()

# To consider separate combinations of factors, we can do something like:
#    for num_factors_to_use in range(1, len(factors) + 1):
#      combos = list(itertools.combinations(factors, num_factors_to_use))
# For example, itertools.combinations(list('abcd'), 2)
# is  [('a', 'b'), ('a', 'c'), ('a', 'd'), ('b', 'c'), ('b', 'd'), ('c', 'd')]
