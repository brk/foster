#!/usr/bin/env python

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

from __future__ import with_statement

import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback

from run_cmd import *

tests_passed = set()
tests_failed = set()

def ensure_dir_exists(dirname):
  if not os.path.exists(dirname):
    return os.mkdir(dirname)
  return True

def extract_expected_input(path):
  """Reads lines from the start of the file at the given path,
     until it sees a line that is not a commented key/value pair."""
  inlines = []
  with open(path, 'r') as f:
    for line in f:
      #print "testing line ", line
      m = re.match(r"//\s*(.+?):\s*(.+)", line)
      if m == None:
        break

      label = m.group(1)
      value = m.group(2)
      if label == "IN":
        inlines.append(value)

  tmpname = 'tmp.input.txt'
  with open(tmpname, 'w') as f:
    f.writelines(inlines)
  return open(tmpname, 'r')

def get_static_libs():
  return "libfoster_main.o libchromium_base.a libcpuid.a libimath.a"

def get_link_flags():
  import platform
  flags = {
    'Darwin': lambda: ['-lpthread', '-framework', 'CoreFoundation'],
    'Linux': lambda: ['-lrt', '-lpthread']
  }[platform.system()]()
  return ' '.join(flags)

def testname(testpath):
  """Given '/path/to/some/test.foster', returns 'test'"""
  return os.path.basename(testpath).replace('.foster', '')

def compile_test_to_bitcode(paths, testpath, compilelog):
    old_style = False

    if old_style:
        fosterc_cmdline = [ paths['fosterc'], testpath, '-O0' ]
        print ' '.join(fosterc_cmdline)
        rv, fc_elapsed = run_command(fosterc_cmdline, paths, testpath, stdout=compilelog, stderr=compilelog)
        return (rv, 0, fc_elapsed, 0)
    else:
        # running fosterparse on a source file produces a ParsedAST
        (s1, e1) = run_command(['fosterparse', testpath, '_out.parsed.pb'], paths, testpath, stdout=compilelog, stderr=compilelog, strictrv=True)

        # running fostercheck on a ParsedAST produces an ElaboratedAST
        (s2, e2) = run_command(['fostercheck', '_out.parsed.pb', '_out.checked.pb'], paths, testpath, stdout=compilelog, stderr=compilelog, strictrv=True)

        # running fosterlower on a ParsedAST produces a bitcode Module
        # linking a bunch of Modules produces a Module
        # Running opt on a Module produces a Module
        # Running llc on a Module produces an assembly file
        (s3, e3) = run_command(['fosterlower', '_out.checked.pb', '-O0'], paths, testpath, stdout=compilelog, stderr=compilelog, strictrv=True)

        return (s3, e1, e2, e3)

def run_one_test(testpath, paths, tmpdir):
  start = walltime()
  exp_filename = os.path.join(tmpdir, "expected.txt")
  act_filename = os.path.join(tmpdir, "actual.txt")
  with open(exp_filename, 'w') as expected:
    with open(act_filename, 'w') as actual:
      with open(os.path.join(tmpdir, "compile.log.txt"), 'w') as compilelog:
        infile = extract_expected_input(testpath)

        rv, fp_elapsed, fc_elapsed, fl_elapsed = compile_test_to_bitcode(paths, testpath, compilelog)

        rv, cc_elapsed = run_command('g++ out.s %s %s -o a.out' % (get_static_libs(), get_link_flags()),
                                    paths, testpath)
        rv, rn_elapsed = run_command('a.out',  paths, testpath, stdout=actual, stderr=expected, stdin=infile, strictrv=False)

        df_rv = subprocess.call(['diff', '-u', exp_filename, act_filename])
        if df_rv == 0:
          tests_passed.add(testpath)
        else:
          tests_failed.add(testpath)

        total_elapsed = elapsed_since(start)
        print "fpr:%4d | foc:%4d | flo:%4d | gcc:%4d | run:%4d | py:%3d | tot:%5d | %s" % (fp_elapsed, fc_elapsed, fl_elapsed,
                        cc_elapsed, rn_elapsed, (total_elapsed - (cc_elapsed + rn_elapsed + fp_elapsed + fc_elapsed + fl_elapsed)),
                        total_elapsed, testname(testpath))
        infile.close()

def main(testpath, paths, tmpdir):
  testdir = os.path.join(tmpdir, testname(testpath))
  if not os.path.isdir(testdir):
    os.makedirs(testdir)
  run_one_test(testpath, paths, testdir)

def get_paths(bindir):
  join = os.path.join
  paths = {
      'out.s':     join(bindir, 'fc-output', 'out.s'),
      'a.out':     join(bindir, 'fc-output', 'a.out'),
  }
  for bin in ['fosterc', 'fosterparse', 'fosterlower', 'fostercheck']:
      paths[bin] = join(bindir, bin)
  for lib in ['libfoster.bc', 'libcpuid.o', 'libfoster_main.o']:
      paths[bin] = join(bindir, bin)

  # compiler spits out foster.ll in current directory
  paths['foster.ll'] = join(os.path.dirname(paths['fosterc']), 'foster.ll')
  return paths

if __name__ == "__main__":
  if not len(sys.argv) in [2, 3]:
    print "Usage: %s <test_path> [project_bin_dir = .]"
    sys.exit(1)

  testpath = sys.argv[1]
  bindir = os.getcwd()
  if len(sys.argv) == 3:
    bindir = sys.argv[2]

  tmpdir = os.path.join(bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)

  main(testpath, get_paths(bindir), tmpdir)
