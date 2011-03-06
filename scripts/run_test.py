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

options = None

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

def nativelib_dir():
  return "_nativelibs_"

def shared(lib):
  import platform
  suffix = {
    'Darwin': ".dylib",
    'Linux':  ".so"
  }[platform.system()]
  return lib + suffix

def get_static_libs():
    return ' '.join([os.path.join(nativelib_dir(), lib) for lib in
         ("libfoster_main.o " + shared("libchromium_base") + " " +
          "libcpuid.a libimath.a libcoro.a").split(" ")])

def get_link_flags():
  common = ['-lpthread']
  import platform
  flags = {
    'Darwin': lambda: common + ['-framework', 'CoreFoundation',
                                '-framework', 'Cocoa',
                                '-lobjc'],
    'Linux': lambda: common + ['-lrt']
  }[platform.system()]()
  return ' '.join(flags)

def testname(testpath):
  """Given '/path/to/some/test.foster', returns 'test'"""
  return os.path.basename(testpath).replace('.foster', '')

def compile_test_to_bitcode(paths, testpath, compilelog, finalpath):
    finalname = os.path.basename(finalpath)
    verbose = options and options.verbose

    # Getting tee functionality in Python is a pain in the behind
    # so we just disable logging when running with --verbose.
    if verbose:
      compilelog = None

    # running fosterparse on a source file produces a ParsedAST
    (s1, e1) = run_command(['fosterparse', testpath, '_out.parsed.pb'],
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # running fostercheck on a ParsedAST produces an ElaboratedAST
    (s2, e2) = run_command(['fostercheck', '_out.parsed.pb', '_out.checked.pb'],
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # running fosterlower on a ParsedAST produces a bitcode Module
    # linking a bunch of Modules produces a Module
    (s3, e3) = run_command(['fosterlower', '_out.checked.pb', '-o', finalname, '-dump-prelinked', '-fosterc-time'],
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # Running opt on a Module produces a Module
    # Running llc on a Module produces an assembly file
    (s4, e4) = run_command(['fosteroptc', finalpath + '.preopt.bc', '-O0', '-fosterc-time'],
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    return (s4, e1, e2, e3, e4)

def run_one_test(testpath, paths, tmpdir):
  start = walltime()
  exp_filename = os.path.join(tmpdir, "expected.txt")
  act_filename = os.path.join(tmpdir, "actual.txt")
  log_filename = os.path.join(tmpdir, "compile.log.txt")
  with open(exp_filename, 'w') as expected:
    with open(act_filename, 'w') as actual:
      with open(log_filename, 'w') as compilelog:
        infile = extract_expected_input(testpath)

        finalpath = os.path.join('fc-output', 'out')
        exepath   = os.path.join('fc-output', 'a.out')

        rv, fp_elapsed, fm_elapsed, fl_elapsed, fc_elapsed = compile_test_to_bitcode(paths, testpath, compilelog, finalpath)

        rv, as_elapsed = run_command(('gcc %s.s -c -o %s.o' % (finalpath, finalpath)),
                                    paths, testpath)
        rv, ld_elapsed = run_command('g++ %s.o %s %s -o %s' % (finalpath, get_static_libs(), get_link_flags(), exepath)
                                    paths, testpath)
        rv, rn_elapsed = run_command(exepath,  paths, testpath, stdout=actual, stderr=expected, stdin=infile, strictrv=False)

        df_rv = subprocess.call(['diff', '-u', exp_filename, act_filename])
        if df_rv == 0:
          tests_passed.add(testpath)
        else:
          tests_failed.add(testpath)

        total_elapsed = elapsed_since(start)
        compile_elapsed = (as_elapsed + ld_elapsed + fp_elapsed + fm_elapsed + fl_elapsed + fc_elapsed)
        overhead = total_elapsed - (compile_elapsed + rn_elapsed)
        print "fpr:%4d | fme:%4d | flo:%4d | foc:%4d | as:%4d | ld:%4d | run:%4d | py:%3d | tot:%5d | %s" % (fp_elapsed, fm_elapsed, fl_elapsed, fc_elapsed,
                        as_elapsed, ld_elapsed, rn_elapsed, overhead, total_elapsed, testname(testpath))

        print "fpr:%3.0f%% | fme:%3.0f%% | flo:%3.0f%% | foc:%3.0f%% | as:%3.0f%% | ld:%3.0f%%" % tuple(100.0*x/float(compile_elapsed) for x in list((fp_elapsed, fm_elapsed, fl_elapsed, fc_elapsed, as_elapsed, ld_elapsed)))
        print "".join("-" for x in range(60))
        infile.close()

  if options and options.verbose:
      run_command(["paste", exp_filename, act_filename], {}, "")


def main(testpath, paths, tmpdir):
  testdir = os.path.join(tmpdir, testname(testpath))
  if not os.path.isdir(testdir):
    os.makedirs(testdir)

  run_one_test(testpath, paths, testdir)

def mkpath(root, prog):
  if os.path.isabs(prog):
    return prog
  else:
    return os.path.join(root, prog)

def get_paths(options, tmpdir):
  join = os.path.join
  bindir = options.bindir
  paths = {
      'bindir':    bindir
  }
  for prog in ['fosterparse', 'fosterlower', 'fosteroptc']:
      paths[prog] = mkpath(bindir, prog)

  for lib in ['libfoster.bc']:
      paths[lib] =  mkpath(bindir, os.path.join('_bitcodelibs_', lib))

  for lib in [ 'libfoster_main.o']:
      paths[lib] =  mkpath(bindir, os.path.join('_nativelibs_', lib))

  for out in ['_out.parsed.pb', '_out.checked.pb']:
      paths[out] =  mkpath(tmpdir, out)

  if options.me != 'fostercheck':
    paths['fostercheck'] = mkpath(bindir, options.me)

  # compiler spits out foster.ll in current directory
  paths['foster.ll'] = join(os.path.dirname(paths['fosterparse']), 'foster.ll')
  return paths

def get_test_parser(usage):
  parser = OptionParser(usage=usage)
  parser.add_option("--bindir", dest="bindir", action="store", default=os.getcwd(),
                    help="Use bindir as default place to find binaries; defaults to current directory")
  parser.add_option("--me", dest="me", action="store", default="me",
                    help="Relative (from bindir) or absolute path to binary to use for type checking.")
  parser.add_option("--verbose", action="store_true", dest="verbose", default=False,
                    help="Show more information about program output.")
  return parser

if __name__ == "__main__":
  parser = get_test_parser("usage: %prog [options] <test_path>")
  (options, args) = parser.parse_args()

  if len(args) != 1:
    print parser.print_help()
    sys.exit(1)

  testpath = args[0]

  tmpdir = os.path.join(options.bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)

  main(testpath, get_paths(options, tmpdir), tmpdir)
