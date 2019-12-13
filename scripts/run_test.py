#!/usr/bin/env python3

# Copyright (c) 2010 Ben Karel. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt



import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback
import math

from run_cmd import *

from fosterc import get_fosterc_parser, fosterc_parser_parse_and_fixup, \
                    compile_foster_code, StopAfterMiddle, fosterc_set_options, \
                    progname, show_cmdlines

from optparse import OptionParser

tests_passed = set()
tests_failed = set()

def ensure_dir_exists(dirname):
  if not os.path.exists(dirname):
    return os.mkdir(dirname)
  return True

def testname(testpath):
  return progname(testpath)

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

# based on http://stackoverflow.com/questions/3758606/how-to-convert-byte-size-into-human-readable-format-in-java/3758880#3758880
def humanized(n, limit=None):
  base = 1024
  if n < base or (limit is not None and n < limit): return str(n) + " B"
  e = int(math.log(n) / math.log(base))
  return "%.1f %sB" % (float(n) / base**e, "KMGTPE"[e - 1])

def aggregate_results(results):
    fields = ["total_elapsed", "compile_elapsed",
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
    print("fpr:%4d | fme:%4d | flo:%4d | foc:%4d | as+ld:%4d | run:%4d | tot:%5d | %s" % (
                res['fp_elapsed'],  res['fm_elapsed'], res['fl_elapsed'], res['fc_elapsed'],
                res['as_elapsed'] + res['ld_elapsed'], res['rn_elapsed'],
                res['total_elapsed'], res['label']))

    # We compute times as a percentage of compile time instead of total time,
    # since these measurements target compilation time, not test case runtime.
    print("fpr:%3.0f%% | fme:%3.0f%% | flo:%3.0f%% | foc:%3.0f%% | as+ld:%3.0f%%" % tuple(
      100.0*x/float(res['compile_elapsed'])
        for x in list((res['fp_elapsed'], res['fm_elapsed'], res['fl_elapsed'],
                       res['fc_elapsed'], res['as_elapsed'] + res['ld_elapsed']))))
    if options.print_bytes_per_sec and 'inbytes' in res:
      print("""input CBOR %(inbytes)s (%(inbytes_per_sec)s/s); output capnp %(ckbytes)s (%(ckbytes_per_sec)s/s); object file %(outbytes)s (%(outbytes_per_sec)s/s)""" % res)
    print("".join("-" for x in range(60)))

def run_diff(a, b):
  "Returns True if diff finds a difference between file a and file b."
  with open(os.devnull, 'w') as devnull:
    (rv, ms) = run_command(['diff', '--brief', a, b], {}, "", stdout=devnull, strictrv=False)
    if rv == 0:
      # same
      if not options.quietish:
        numlines = len(open(a, 'r').readlines())
        print("""

        \m/_(>_<)_\m/    (%d lines)

""" % numlines)
      return False
    else:
      if not options.quietish:
        cmd = ['diff', '--side-by-side', '--left-column', a, b]
        print(' '.join(cmd))
        subprocess.call(cmd)
      return True

def get_prog_stdin(testpath, tmpdir):
  if options.prog_stdin != "":
    return open(options.prog_stdin, 'r')
  else:
    return extract_expected_input(testpath, tmpdir)

def file_size(path):
  try:
    return os.stat(path).st_size
  except:
    return 0

def run_one_test(testpath, tmpdir, progargs, paths, exe_cmd, elapseds):
  exp_filename = os.path.join(tmpdir, "expected.txt")
  act_filename = os.path.join(tmpdir, "actual.txt")
  iact_filename = os.path.join(tmpdir, "istdout.txt")
  rv = 0
  with open(exp_filename, 'w') as expected:
   with open(act_filename, 'w') as actual:
    with get_prog_stdin(testpath, tmpdir) as infile:
      rv, rn_elapsed = run_command(exe_cmd, paths, testpath,
                                 stdout=actual, stderr=expected, stdin=infile,
                                 showcmd=(not options.quietish), strictrv=False)

  inbytes  = file_size(paths['_out.parsed.cbor'])
  ckbytes  = file_size(paths['_out.checked.pb'] + '.cb')
  outbytes = file_size(paths['_out.o'])

  if rv == 0:
    did_fail = run_diff(exp_filename, act_filename)
    if (not did_fail) and options and options.interpret:
      did_fail = run_diff(act_filename, iact_filename)
      if did_fail:
        print("Interpreter output differed!")
  else:
    did_fail = True

  if options.show_stdout:
    with open(act_filename, 'r') as act:
      print(act.read(), end='')

  def elapsed_per_sec(b, e): return humanized(float(b)/(float(e) / 1000.0))
  (fp_elapsed, fm_elapsed, fl_elapsed, fc_elapsed, as_elapsed, ld_elapsed) = elapseds
  compile_elapsed = (as_elapsed + ld_elapsed + fp_elapsed + fm_elapsed + fl_elapsed + fc_elapsed)
  total_elapsed = rn_elapsed + compile_elapsed
  result = dict(failed=did_fail, label=testname(testpath),
                total_elapsed=total_elapsed,
                compile_elapsed=compile_elapsed,
                inbytes=humanized(inbytes, limit=10000),
                ckbytes=humanized(ckbytes, limit=10000),
                outbytes=humanized(outbytes, limit=10000),
                inbytes_per_sec=elapsed_per_sec(inbytes, fp_elapsed),
                ckbytes_per_sec=elapsed_per_sec(ckbytes, fm_elapsed),
                outbytes_per_sec=elapsed_per_sec(outbytes, fl_elapsed + fc_elapsed),
    fp_elapsed=fp_elapsed, fm_elapsed=fm_elapsed, fl_elapsed=fl_elapsed,
    fc_elapsed=fc_elapsed, as_elapsed=as_elapsed, ld_elapsed=ld_elapsed, rn_elapsed=rn_elapsed)
  infile.close()

  if rv != 0:
    print(testpath, "failed with non-zero return value", rv)

  return result


def classify_result(result, testpath):
  if result['failed']:
    tests_failed.add(testpath)
  else:
    tests_passed.add(testpath)

def mkpath(root, prog):
  if os.path.isabs(prog):
    return prog
  else:
    return os.path.join(root, prog)

def get_test_parser():
  parser = get_fosterc_parser()
  parser.add_option("--quietish", dest="quietish", action="store_true", default=False,
                    help="Run test(s) with less output")
  parser.add_option("--show-stdout", dest="show_stdout", action="store_true", default=False,
                    help="Print the program's stdout after it terminates")
  return parser

def test_parser_parse_and_fixup(parser):
  return fosterc_parser_parse_and_fixup(parser)

def compile_and_run_test(testpath, testdir):
  options.tmpdir = testdir
  (paths, exe_cmd, elapseds) = compile_foster_code(testpath)
  return run_one_test(testpath, testdir, options.progargs, paths, exe_cmd, elapseds)

def test_set_options(opts):
  global options
  options = opts
  fosterc_set_options(opts)

if __name__ == "__main__":
  parser = get_test_parser()
  (options, args) = test_parser_parse_and_fixup(parser)

  if len(args) != 1:
    print(args)
    print(options)
    print(parser.print_help())
    sys.exit(1)

  testpath = args[0]

  tmpdir = os.path.join(options.bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)

  testdir = os.path.join(tmpdir, testname(testpath))
  ensure_dir_exists(testdir)

  # Note: we rely on options being mutable.
  fosterc_set_options(options)

  try:
    result = compile_and_run_test(testpath, testdir)
    if not options.quietish:
      print_result_table(result)
    classify_result(result, testpath)
  except StopAfterMiddle:
    pass
