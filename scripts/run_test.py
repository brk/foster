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
    'Darwin': lambda: '',
    'Linux' : lambda: '-Wl,-R,' + os.path.abspath(path),
  }[platform.system()]()


def testname(testpath):
  """Given '/path/to/some/test.foster', returns 'test'"""
  return os.path.basename(testpath).replace('.foster', '')

def output_extension(to_asm):
  if to_asm:
    return ".s"
  else:
    return ".o"

def show_cmdlines(options):
  return options and options.show_cmdlines == True

def optlevel(options):
  if options and options.optlevel:
    # Right now fosteroptc only recognizes -O0, not -O2 or such.
    # So if we don't disable optimizations, we probably want to
    # see the optimized LLVM IR.
    return '-dump-postopt'
  else:
    return '-O0'

def compile_test_to_bitcode(paths, testpath, compilelog, finalpath, tmpdir):
    finalname = os.path.basename(finalpath)
    to_asm = options and options.asm
    ext = output_extension(to_asm)

    # Getting tee functionality in Python is a pain in the behind
    # so we just disable logging when running with --show-cmdlines.
    if show_cmdlines(options):
      compilelog = None

    if options and options.importpath:
      importpath = ["-I", options.importpath]
    else:
      importpath = []

    if options and options.interpret:
      interpret = ["--interpret", tmpdir]
    else:
      interpret = []

    ghc_rts_args = ["-smeGCstats.txt"]

    if options and options.profile:
      ghc_rts_args.append("-p")
      ghc_rts_args.append("-hc")

    parse_output = os.path.join(tmpdir, '_out.parsed.pb')
    check_output = os.path.join(tmpdir, '_out.checked.pb')

    def crun(cmdlist):
      return run_command(cmdlist,
                paths, testpath, showcmd=show_cmdlines(options),
                stdout=compilelog, stderr=compilelog, strictrv=True)

    # running fosterparse on a source file produces a ParsedAST
    (s1, e1) = crun(['fosterparse', testpath, parse_output] + importpath)

    # running fostercheck on a ParsedAST produces an ElaboratedAST
    prog_args = [arg for _arg in options.progargs or []
                     for arg in ['--prog-arg', _arg]]
    (s2, e2) = crun(['fostercheck', parse_output, check_output] +
                     ["+RTS"] + ghc_rts_args + ["-RTS"] +
                     interpret + options.meargs + prog_args)

    # running fosterlower on a ParsedAST produces a bitcode Module
    # linking a bunch of Modules produces a Module
    (s3, e3) = crun(['fosterlower', check_output, '-o', finalname,
                         '-outdir', tmpdir, '-dump-prelinked', '-fosterc-time']
                    + options.beargs)

    # Running opt on a Module produces a Module
    # Running llc on a Module produces an assembly file
    (s4, e4) = crun(['fosteroptc', finalpath + '.preopt.bc',
                               optlevel(options), '-fosterc-time', '-o', finalpath + ext])

    return (s4, to_asm, e1, e2, e3, e4)

def link_to_executable(finalpath, exepath, paths, testpath):
    return run_command('g++ %(finalpath)s.o %(staticlibs)s %(linkflags)s -o %(exepath)s %(rpath)s' % {
                         'finalpath' : finalpath,
                         'staticlibs': get_static_libs(),
                         'linkflags' : get_link_flags(),
                         'exepath'   : exepath,
                         'rpath'     : rpath(nativelib_dir())
                       },  paths, testpath)

def aggregate_results(results):
    fields = ["total_elapsed", "compile_elapsed", "overhead",
              "fp_elapsed", "fm_elapsed", "fl_elapsed",
              "fc_elapsed", "as_elapsed", "ld_elapsed", "rn_elapsed",]
    result = dict(failed=False, label="<aggregate results>",
                  total_elapsed=0, compile_elapsed=0, overhead=0,
                  fp_elapsed=0, fm_elapsed=0, fl_elapsed=0,
                  fc_elapsed=0, as_elapsed=0, ld_elapsed=0, rn_elapsed=0)
    for res in results:
        for field in fields:
            result[field] += res[field]
    return result

def print_result_table(res):
    print "fpr:%4d | fme:%4d | flo:%4d | foc:%4d | as:%4d | ld:%4d | run:%4d | py:%3d | tot:%5d | %s" % (
                res['fp_elapsed'], res['fm_elapsed'], res['fl_elapsed'], res['fc_elapsed'],
                res['as_elapsed'], res['ld_elapsed'], res['rn_elapsed'],
                res['overhead'], res['total_elapsed'], res['label'])

    # We compute times as a percentage of compile time instead of total time,
    # since these measurements target compilation time, not test case runtime.
    print "fpr:%3.0f%% | fme:%3.0f%% | flo:%3.0f%% | foc:%3.0f%% | as:%3.0f%% | ld:%3.0f%%" % tuple(
      100.0*x/float(res['compile_elapsed'])
        for x in list((res['fp_elapsed'], res['fm_elapsed'], res['fl_elapsed'],
                       res['fc_elapsed'], res['as_elapsed'], res['ld_elapsed'])))
    print "".join("-" for x in range(60))

def run_diff(a, b):
  "Returns True if diff finds a difference between file a and file b."
  df_rv = subprocess.call(['diff', '-u', a, b])
  return df_rv != 0

def run_one_test(testpath, paths, tmpdir, progargs):
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
          rv, as_elapsed = run_command('gcc %s.s -c -o %s.o' % (finalpath, finalpath), paths, testpath)
        else: # fosteroptc emitted a .o directly.
          as_elapsed = 0


        rv, ld_elapsed = link_to_executable(finalpath, exepath, paths, testpath)
        rv, rn_elapsed = run_command([exepath] + progargs, paths, testpath,
                                     stdout=actual, stderr=expected, stdin=infile, strictrv=False)

  if rv == 0:
    did_fail = run_diff(exp_filename, act_filename)
    if (not did_fail) and options and options.interpret:
      did_fail = run_diff(act_filename, iact_filename)
      if did_fail:
        print "Interpreter output differed!"
  else:
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

  if show_cmdlines(options):
    run_command(["paste", exp_filename, act_filename], {}, "")

  if rv != 0:
    print exepath, "failed with non-zero return value", rv

  return result


def classify_result(result, testpath):
  if result['failed']:
    tests_failed.add(testpath)
  else:
    tests_passed.add(testpath)

def main(testpath, paths, tmpdir, progargs):
  testdir = os.path.join(tmpdir, testname(testpath))
  if not os.path.isdir(testdir):
    os.makedirs(testdir)

  result = run_one_test(testpath, paths, testdir, progargs)
  print_result_table(result)
  classify_result(result, testpath)

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
  parser.add_option("--show-cmdlines", action="store_true", dest="show_cmdlines", default=False,
                    help="Show more information about programs being run.")
  parser.add_option("--asm", action="store_true", dest="asm", default=False,
                    help="Compile to assembly rather than object file.")
  parser.add_option("--interpret", action="store_true", dest="interpret", default=False,
                    help="Run using interpreter instead of compiling via LLVM")
  parser.add_option("--optimize", dest="optlevel", default=False,
                    help="Enable optimizations in fosteroptc")
  parser.add_option("--profile", dest="profile", default=False,
                    help="Enable detailed profiling of compiler middle-end")
  parser.add_option("--me-arg", action="append", dest="meargs", default=[],
                    help="Pass through arg to middle-end.")
  parser.add_option("--be-arg", action="append", dest="beargs", default=[],
                    help="Pass through arg to back-end.")
  parser.add_option("--prog-arg", action="append", dest="progargs", default=[],
                    help="Pass through command line arguments to program")
  parser.add_option("-I", dest="importpath", action="store", default=None,
                    help="Set import path")
  return parser

if __name__ == "__main__":
  parser = get_test_parser("""usage: %prog [options] <test_path>

   Notes:
     * If using ./gotest.sh, --me-arg=--verbose       will print (Ann)ASTs
                             --me-arg=--dump-ir=kn    will print k-normalized IR
                             --me-arg=--dump-ir=cfg   will print closure-conv IR
                             --me-arg=--dump-ir=mono  will print monomo. IR
""")
  (options, args) = parser.parse_args()

  if len(args) != 1:
    print args
    print options
    print parser.print_help()
    sys.exit(1)

  testpath = args[0]

  tmpdir = os.path.join(options.bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)

  main(testpath, get_paths(options, tmpdir), tmpdir, options.progargs)
