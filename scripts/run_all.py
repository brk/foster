from __future__ import with_statement
import time
import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback
import multiprocessing
import itertools

import run_test
from list_all import collect_all_tests

def run_and_print_test(testpath, tmpdir, paths):
  try:
    test_tmpdir = os.path.join(tmpdir, run_test.testname(testpath))
    result = run_test.run_one_test(testpath, paths, test_tmpdir)
    run_test.print_result_table(result)
    run_test.classify_result(result, testpath)
  except run_test.TestFailed:
    run_test.tests_failed.add(testpath)

def run_all_tests_slow(bootstrap_dir, paths, tmpdir):
  tests = collect_all_tests(bootstrap_dir)
  for testpath in tests:
    try:
      run_and_print_test(testpath, tmpdir, paths)
    except KeyboardInterrupt:
      return

def worker_run_test(info):
  testpath, tmpdir, paths = info
  try:
    test_tmpdir = os.path.join(tmpdir, run_test.testname(testpath))
    result = run_test.run_one_test(testpath, paths, test_tmpdir)
    return (testpath, result)
  except KeyboardInterrupt:
    return (testpath, None) # Workers should ignore keyboard interrupts
  except run_test.TestFailed:
    return (testpath, None)

def run_all_tests_fast(bootstrap_dir, paths, tmpdir):
  tests = collect_all_tests(bootstrap_dir)
  pool = multiprocessing.Pool()
  try:
    for result in pool.imap_unordered(worker_run_test,
                itertools.izip(tests,
                  itertools.repeat(tmpdir),
                  itertools.repeat(paths))):
       testpath, result = result
       if result is not None:
         run_test.print_result_table(result)
         run_test.classify_result(result, testpath)
       else:
         run_test.tests_failed.add(testpath)
  except KeyboardInterrupt:
    return

def main(opts, bootstrap_dir, paths, tmpdir):
  walkstart = run_test.walltime()

  if should_run_tests_in_parallel(opts):
    run_all_tests_fast(bootstrap_dir, paths, tmpdir)
  else:
    run_all_tests_slow(bootstrap_dir, paths, tmpdir)

  walkend = run_test.walltime()
  print "Total time: %d ms" % run_test.elapsed(walkstart, walkend)

  print len(run_test.tests_passed), " tests passed"

  print len(run_test.tests_failed), " tests failed"
  if len(run_test.tests_failed) > 0:
    for test in run_test.tests_failed:
      print test
  sys.exit(len(run_test.tests_failed))

def should_run_tests_in_parallel(options):
  if options.parallel:
    return True

  if options.serial:
     return False

  import platform
  if platform.system() == "Darwin":
    # Mac OS X doesn't seem to maintain a consistent
    # view of file contents when written from a process
    # spawned by a multiprocessing.Pool worker, and
    # subsequently read by the same worker.
    return False

  # By default, run tests in parallel.
  return True

if __name__ == "__main__":
  parser = run_test.get_test_parser("usage: %prog [options] <bootstrap_test_dir>")
  parser.add_option("--parallel", dest="parallel", action="store_true", default=False,
                    help="Run tests in parallel")
  parser.add_option("--serial", dest="serial", action="store_true", default=False,
                    help="Run tests in serial")
  (opts, args) = parser.parse_args()

  if len(args) == 0:
    print "Missing <bootstrap_test_dir>!"
    parser.print_help()
    sys.exit(1)

  run_test.options = opts
  bootstrap_dir = args[0]

  tmpdir = os.path.join(opts.bindir, 'test-tmpdir')
  run_test.ensure_dir_exists(tmpdir)

  main(opts, bootstrap_dir, run_test.get_paths(opts, tmpdir), tmpdir)
