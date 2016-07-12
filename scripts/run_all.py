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

all_results = []

def handle_successful_test_result(result, testpath):
    if opts.quietish:
      print os.path.basename(testpath)
    else:
      run_test.print_result_table(result)
    run_test.classify_result(result, testpath)
    all_results.append(result)

def run_and_print_test(testpath, tmpdir):
  try:
    testdir = os.path.join(tmpdir, run_test.testname(testpath))
    run_test.ensure_dir_exists(testdir)
    result = run_test.compile_and_run_test(testpath, testdir)
    handle_successful_test_result(result, testpath)
  except run_test.TestFailed:
    run_test.tests_failed.add(testpath)

def run_all_tests_slow(tests, bootstrap_dir, tmpdir):
  for testpath in tests:
    try:
      run_and_print_test(testpath, tmpdir)
    except KeyboardInterrupt:
      return

def worker_run_test(info):
  testpath, tmpdir = info
  try:
    testdir = os.path.join(tmpdir, run_test.testname(testpath))
    run_test.ensure_dir_exists(testdir)
    result = run_test.compile_and_run_test(testpath, testdir)
    return (testpath, result)
  except KeyboardInterrupt:
    return (testpath, None) # Workers should ignore keyboard interrupts
  except run_test.TestFailed:
    return (testpath, None)

def run_all_tests_fast(tests, bootstrap_dir, tmpdir):
  pool = multiprocessing.Pool()
  try:
    for result in pool.imap_unordered(worker_run_test,
                itertools.izip(tests,
                  itertools.repeat(tmpdir))):
       testpath, result = result
       if result is not None:
         handle_successful_test_result(result, testpath)
       else:
         run_test.tests_failed.add(testpath)
  except KeyboardInterrupt:
    return

def main(opts, bootstrap_dir, tmpdir):
  walkstart = run_test.walltime()
  tests = collect_all_tests(bootstrap_dir)
  if should_run_tests_in_parallel(opts):
    run_all_tests_fast(tests, bootstrap_dir, tmpdir)
  else:
    run_all_tests_slow(tests, bootstrap_dir, tmpdir)
  walkend = run_test.walltime()

  run_test.print_result_table(run_test.aggregate_results(all_results))

  print "Total (wall-clock) time: %d ms" % run_test.elapsed(walkstart, walkend)

  print len(run_test.tests_passed), " tests passed"

  print len(run_test.tests_failed), " tests failed"
  if len(run_test.tests_failed) > 0:
    for test in run_test.tests_failed:
      print test

  num_tests_attempted = len(run_test.tests_passed) + len(run_test.tests_failed)
  num_tests_not_attempted = len(tests) - num_tests_attempted
  if num_tests_not_attempted > 0:
    print num_tests_not_attempted, " tests not reached"

  try:
    from stathat import StatHat
    sh = StatHat()
    # tests run - counter
    sh.post_count('MjQ2IBSJUNLO7SpS4kttBQFHp2w~', '3TW60dh1mJQIqFql3VSaQSBqYlVJ', len(run_test.tests_passed))
    # time taken - ms
    sh.post_value('MjQ2IBSJUNLO7SpS4kttBQFHp2w~', 'OIy1N3KRYp84fRyXl-GljSA1enpW', run_test.elapsed(walkstart, walkend))
  except:
    pass

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
  parser = run_test.get_test_parser()
  parser.add_option("--parallel", dest="parallel", action="store_true", default=False,
                    help="Run tests in parallel")
  parser.add_option("--serial", dest="serial", action="store_true", default=False,
                    help="Run tests in serial")
  (opts, args) = run_test.test_parser_parse_and_fixup(parser)

  if len(args) == 0:
    print "Missing <bootstrap_test_dir>!"
    parser.print_help()
    sys.exit(1)

  run_test.test_set_options(opts)

  bootstrap_dir = args[0]

  tmpdir = os.path.join(opts.bindir, 'test-tmpdir')
  run_test.ensure_dir_exists(tmpdir)

  main(opts, bootstrap_dir, tmpdir)
