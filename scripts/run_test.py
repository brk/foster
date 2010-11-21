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

from optparse import OptionParser

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

        rv, as_elapsed = run_command('g++ out.s -c -o out.o', paths, testpath)
        rv, ld_elapsed = run_command('g++ out.o %s %s -o a.out' % (get_static_libs(), get_link_flags()),
                                    paths, testpath)
        rv, rn_elapsed = run_command('a.out',  paths, testpath, stdout=actual, stderr=expected, stdin=infile, strictrv=False)

        df_rv = subprocess.call(['diff', '-u', exp_filename, act_filename])
        if df_rv == 0:
          tests_passed.add(testpath)
        else:
          tests_failed.add(testpath)

        total_elapsed = elapsed_since(start)
        compile_elapsed = (as_elapsed + ld_elapsed + fp_elapsed + fc_elapsed + fl_elapsed)
        overhead = total_elapsed - (compile_elapsed + rn_elapsed)
        print "fpr:%4d | foc:%4d | flo:%4d | as:%4d | ld:%4d | run:%4d | py:%3d | tot:%5d | %s" % (fp_elapsed, fc_elapsed, fl_elapsed,
                        as_elapsed, ld_elapsed, rn_elapsed, overhead, total_elapsed, testname(testpath))

        print "fpr:%3.0f%% | foc:%3.0f%% | flo:%3.0f%% | as:%3.0f%% | ld:%3.0f%%" % tuple(100.0*x/float(compile_elapsed) for x in list((fp_elapsed, fc_elapsed, fl_elapsed, as_elapsed, ld_elapsed)))
        print "".join("-" for x in range(60))
        infile.close()

def main(testpath, paths, tmpdir):
  testdir = os.path.join(tmpdir, testname(testpath))
  if not os.path.isdir(testdir):
    os.makedirs(testdir)
  run_one_test(testpath, paths, testdir)

def binpath(bindir, prog):
  if os.path.isabs(prog):
    return prog
  else:
    return os.path.join(bindir, prog)

def get_paths(bindir, options):
  join = os.path.join
  paths = {
      'out.s':     join(bindir, 'fc-output', 'out.s'),
      'a.out':     join(bindir, 'fc-output', 'a.out'),
  }
  for prog in ['fosterc', 'fosterparse', 'fosterlower', 'fostercheck']:
      paths[prog] = binpath(bindir, prog)
  for lib in ['libfoster.bc', 'libcpuid.o', 'libfoster_main.o']:
      paths[lib] = binpath(bindir, lib)

  if options.me != 'fostercheck':
    paths['fostercheck'] = binpath(bindir, options.me)

  # compiler spits out foster.ll in current directory
  paths['foster.ll'] = join(os.path.dirname(paths['fosterc']), 'foster.ll')
  return paths

def get_test_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--bindir", dest="bindir", action="store", default=os.getcwd(),
                    help="Use bindir as default place to find binaries; defaults to current directory")
  parser.add_option("--me", dest="me", action="store", default="fostercheck",
                    help="Relative (from bindir) or absolute path to binary to use for type checking.")
  return parser

if __name__ == "__main__":
  parser = get_test_parser("usage: %prog [options] <test_path>")
  (options, args) = parser.parse_args()

  if len(args) != 1:
    print parser.print_help()
    sys.exit(1)

  testpath = args[0]
  bindir = options.bindir

  tmpdir = os.path.join(bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)

  main(testpath, get_paths(bindir, options), tmpdir)
