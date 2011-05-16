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

def extract_expected_input(path, rootdir):
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

  tmpname = os.path.join(rootdir, '_extracted_input.txt')
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

def rpath(path):
  import platform
  return {
    'Darwin': lambda: "",
    'Linux' : lambda:  ' -Wl,-R,' + os.path.abspath(path),
  }[platform.system()]()


def testname(testpath):
  """Given '/path/to/some/test.foster', returns 'test'"""
  return os.path.basename(testpath).replace('.foster', '')

def compile_test_to_bitcode(paths, testpath, compilelog, finalpath, tmpdir):
    finalname = os.path.basename(finalpath)
    verbose = options and options.verbose
    to_asm  = options and options.asm

    if to_asm:
      ext = ".s"
    else:
      ext = ".o"

    # Getting tee functionality in Python is a pain in the behind
    # so we just disable logging when running with --verbose.
    if verbose:
      compilelog = None
      verbosearg = ["--verbose"]
    else:
      verbosearg = []

    if options and options.interpret:
      interpret = ["--interpret", tmpdir]
    else:
      interpret = []

    optlevel = '-O0'
    if options and options.optlevel:
      # Right now fosteroptc only recognizes -O0, not -O2 or such.
      # So if we don't disable optimizations, we probably want to
      # see the optimized LLVM IR.
      optlevel = '-dump-postopt'

    parse_output = os.path.join(tmpdir, '_out.parsed.pb')
    check_output = os.path.join(tmpdir, '_out.checked.pb')

    # running fosterparse on a source file produces a ParsedAST
    (s1, e1) = run_command(['fosterparse', testpath, parse_output],
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # running fostercheck on a ParsedAST produces an ElaboratedAST
    (s2, e2) = run_command(['fostercheck', parse_output, check_output] + interpret + verbosearg,
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # running fosterlower on a ParsedAST produces a bitcode Module
    # linking a bunch of Modules produces a Module
    (s3, e3) = run_command(['fosterlower', check_output, '-o', finalname,
                            '-outdir', tmpdir, '-dump-prelinked', '-fosterc-time'],
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # Running opt on a Module produces a Module
    # Running llc on a Module produces an assembly file
    (s4, e4) = run_command(['fosteroptc', finalpath + '.preopt.bc',
                               optlevel, '-fosterc-time', '-o', finalpath + ext],
                paths, testpath, showcmd=verbose,
                stdout=compilelog, stderr=compilelog, strictrv=True)

    return (s4, to_asm, e1, e2, e3, e4)

def print_result_table(res):
    print "fpr:%4d | fme:%4d | flo:%4d | foc:%4d | as:%4d | ld:%4d | run:%4d | py:%3d | tot:%5d | %s" % (
                res['fp_elapsed'], res['fm_elapsed'], res['fl_elapsed'], res['fc_elapsed'],
                res['as_elapsed'], res['ld_elapsed'], res['rn_elapsed'],
                res['overhead'], res['total_elapsed'], res['label'])

    print "fpr:%3.0f%% | fme:%3.0f%% | flo:%3.0f%% | foc:%3.0f%% | as:%3.0f%% | ld:%3.0f%%" % tuple(100.0*x/float(res['compile_elapsed'])
        for x in list((res['fp_elapsed'], res['fm_elapsed'], res['fl_elapsed'],
                       res['fc_elapsed'], res['as_elapsed'], res['ld_elapsed'])))
    print "".join("-" for x in range(60))

def run_one_test(testpath, paths, tmpdir):
  ensure_dir_exists(tmpdir)
  start = walltime()
  exp_filename = os.path.join(tmpdir, "expected.txt")
  act_filename = os.path.join(tmpdir, "actual.txt")
  log_filename = os.path.join(tmpdir, "compile.log.txt")
  iact_filename = os.path.join(tmpdir, "istdout.txt")
  with open(exp_filename, 'w') as expected:
    with open(act_filename, 'w') as actual:
      with open(log_filename, 'w') as compilelog:
        infile = extract_expected_input(testpath, tmpdir)

        finalpath = os.path.join(tmpdir, 'out')
        exepath   = os.path.join(tmpdir, 'a.out')

        rv, to_asm, fp_elapsed, fm_elapsed, fl_elapsed, fc_elapsed = \
                compile_test_to_bitcode(paths, testpath, compilelog, finalpath, tmpdir)

        if to_asm:
          rv, as_elapsed = run_command('gcc %s.s -c -o %s.o' % (finalpath, finalpath),
                                      paths, testpath)
        else:
          as_elapsed = 0

        rv, ld_elapsed = run_command('g++ %s.o %s %s -o %s' % (finalpath, get_static_libs(), get_link_flags(), exepath)
                                    + rpath(nativelib_dir()),
                                    paths, testpath)
        rv, rn_elapsed = run_command(exepath,  paths, testpath, stdout=actual, stderr=expected, stdin=infile, strictrv=False)

  did_fail = False
  df_rv = subprocess.call(['diff', '-u', exp_filename, act_filename])
  if df_rv != 0:
    did_fail = True
  elif options and options.interpret:
    df_rv = subprocess.call(['diff', '-u', act_filename, iact_filename])
    if df_rv != 0:
      did_fail = True

  total_elapsed = elapsed_since(start)
  compile_elapsed = (as_elapsed + ld_elapsed + fp_elapsed + fm_elapsed + fl_elapsed + fc_elapsed)
  overhead = total_elapsed - (compile_elapsed + rn_elapsed)
  result = dict(failed=did_fail, label=testname(testpath),
                total_elapsed=total_elapsed,
                compile_elapsed=compile_elapsed, overhead=overhead,
    fp_elapsed=fp_elapsed, fm_elapsed=fm_elapsed, fl_elapsed=fl_elapsed,
    fc_elapsed=fc_elapsed, as_elapsed=as_elapsed, ld_elapsed=ld_elapsed, rn_elapsed=rn_elapsed)
  infile.close()

  if options and options.verbose:
      run_command(["paste", exp_filename, act_filename], {}, "")
  return result


def main(testpath, paths, tmpdir):
  testdir = os.path.join(tmpdir, testname(testpath))
  if not os.path.isdir(testdir):
    os.makedirs(testdir)

  result = run_one_test(testpath, paths, testdir)
  print_result_table(result)

  if result['failed']:
    tests_failed.add(testpath)
  else:
    tests_passed.add(testpath)

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
  parser.add_option("--asm", action="store_true", dest="asm", default=False,
                    help="Compile to assembly rather than object file.")
  parser.add_option("--interpret", action="store_true", dest="interpret", default=False,
                    help="Run using interpreter instead of compiling via LLVM")
  parser.add_option("--optimize", dest="optlevel", default=False,
                    help="Enable optimizations in fosteroptc")

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
