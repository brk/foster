#!/usr/bin/env python

# Copyright (c) 2015 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

import yaml
import subprocess
from jinja2 import Template
from collections import defaultdict
import itertools
import re
import os.path
import sys

import run_cmd

from optparse import OptionParser

_scripts_dir = os.path.dirname(sys.argv[0])

def load(jsonpath):
  with open(jsonpath, 'r') as jsonfile:
    return yaml.safe_load(jsonfile)

def get_test_parser(usage):
  parser = OptionParser(usage=usage)
  return parser

def remove_date(tagstr):
  return re.sub('date=....-..-..@........', 'date=_', tagstr)

def reorganize(json):
  rv = {}
  for x in json:
    test = x['test']
    tags = remove_date(x['tags'])
    inp  = x['input']
    rv[ (test, inp, tags) ] = x
  return rv

def diff_instance_outputs(oldoutputs, newoutputs, name, results):
  oldvals = oldoutputs[name]
  newvals = newoutputs[name]

  if oldvals == newvals:
    pass
  else:
    with open('old_', 'w') as oldfile:
      for v in oldvals:
        oldfile.write('%s\n' % str(v))
    with open('new_', 'w') as newfile:
      for v in newvals:
        newfile.write('%s\n' % str(v))

    output = subprocess.check_output('ministat -A -c 98 old_ new_', shell=True)
    lines = output.split('\n')
    if lines[-2] == 'No difference proven at 98.0% confidence':
      pass
    else:
      old_median = lines[-7].split()[5]
      new_median = lines[-6].split()[5]
      abs_diff = lines[-4].strip()
      rel_diff = lines[-3].strip()
      results.append( (name, rel_diff, abs_diff, old_median, new_median ) )

    #with open('boot.txt', 'w') as boot:
    #  boot.write('old new\n')
    #  for ov, nv in zip( oldvals, newvals ):
    #    boot.write('%s %s\n' % (str(ov), str(nv)))
    #subprocess.call('python bootstrap.py boot.txt --bootstrap', shell=True)

class bcolors:
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'

def parse_result(res):
  """res is a string like '-6.39397% +/- 4.50149%'"""
  pieces = res.split(' ')
  delta     = float(pieces[0][:-1])
  errmargin = float(pieces[2][:-1])
  return (delta, errmargin)

def seems_superfluous(parsedres):
  (delta, errmargin) = parsedres
  return (errmargin > 0.96 * abs(delta))

def seems_noisy(parsedres):
  (delta, errmargin) = parsedres
  return (errmargin > 0.5 * abs(delta))

def maybe_compare_opcode_mixes(results, old_opcodemix, new_opcodemix):
  if len(results) > 0:
    maybe_summarize = ['--summarize']
  else:
    maybe_summarize = []

  if os.path.exists(old_opcodemix):
    if os.path.exists(new_opcodemix):
      run_cmd.run_cmd(['python', os.path.join(_scripts_dir, 'compare-opcodemix.py'),
                                 old_opcodemix, new_opcodemix,
                                 '--ratio', '1.01'] + maybe_summarize)

outputs_to_skip = {
  'Mutator_runtime_s':True,
  '     GC_runtime_s':True,
  'Elapsed_runtime_s':True,
  'Initlzn_runtime_s':True,
  'tot_hms':True,
}

def diff_instances(oi, olddir, ni, newdir, testname, tags):
  oldoutputs = oi['outputs']
  newoutputs = ni['outputs']

  results = []
  common_output_names = list(set(oldoutputs.keys()).intersection(set(newoutputs.keys())))
  for n in common_output_names:
    if n in outputs_to_skip or (n == 'py_run_ms' and 'Elapsed_runtime_ms' in common_output_names):
      pass
    else:
      diff_instance_outputs(oldoutputs, newoutputs, n, results) # testname, tags)

  if len(results) > 0:
    print "%-50s: %s" % (testname, tags)
    for res in results:
      (outnm, rel_diff, abs_diff, old_median, new_median) = res
      outline = "    %-20s:       %30s" % ( "'%s'" % outnm, rel_diff)
      outline2 = " from %10s -> %10s (%s)" % (old_median, new_median, abs_diff)
      parsed_rel_diff = parse_result(rel_diff)
      if seems_superfluous(parsed_rel_diff):
        pass
      elif seems_noisy(parsed_rel_diff):
        print bcolors.OKGREEN, outline, bcolors.ENDC, outline2
      else:
        print bcolors.BOLD, outline, bcolors.ENDC, outline2

  old_opcodemix = os.path.join(olddir, testname.replace('/', '__'), oi['tags'], 'opcodemix.out')
  new_opcodemix = os.path.join(newdir, testname.replace('/', '__'), ni['tags'], 'opcodemix.out')
  maybe_compare_opcode_mixes(results, old_opcodemix, new_opcodemix)

  if len(results) > 0:
    print

def diff_all_instances(newdir, newinsts, olddir, oldinsts):
  common_keys = list(set(newinsts.keys()).intersection(set(oldinsts.keys())))
  for k in common_keys:
    nm, inp, tags = k
    diff_instances(oldinsts[k], olddir, newinsts[k], newdir, nm, tags)

def examine(inst):
  outputs = inst['outputs']
  print outputs

if __name__ == "__main__":
  parser = get_test_parser("""usage: %prog [old path] [new path]\n""")
  (options, args) = parser.parse_args()

  if len(args) == 2:
    pass
  else:
    print "Perhaps invoke with `find data -maxdepth 1 -mindepth 1 -type d | sort | tail -n 2`?"
    import sys
    sys.exit(1)

  olddir = args[0]
  newdir = args[1]

  print 'loading...'
  oldtimings = load(os.path.join(olddir, 'all_timings.json'))
  newtimings = load(os.path.join(newdir, 'all_timings.json'))

  print 'reorganizing...'
  newinsts = reorganize(newtimings)
  oldinsts = reorganize(oldtimings)

  print 'diffing...'
  diff_all_instances(newdir, newinsts, olddir, oldinsts)


