from __future__ import with_statement
import time
import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback

import run_test
from list_all import collect_all_tests

def run_and_print_test(testpath, tmpdir, paths):
  try:
    test_tmpdir = os.path.join(tmpdir, run_test.testname(testpath))
    result = run_test.run_one_test(testpath, paths, test_tmpdir)
    result.print_table()
  except run_test.TestFailed:
    run_test.tests_failed.add(testpath)
      
def run_all_tests(bootstrap_dir, paths, tmpdir):
  tests = collect_all_tests(bootstrap_dir)
  for testpath in tests:
    try:
      run_and_print_test(testpath, tmpdir, paths)
    except KeyboardInterrupt:
      return

def main(bootstrap_dir, paths, tmpdir):
  walkstart = run_test.walltime()
  run_all_tests(bootstrap_dir, paths, tmpdir)
  walkend = run_test.walltime()
  print "Total time: %d ms" % run_test.elapsed(walkstart, walkend)

  print len(run_test.tests_passed), " tests passed"

  print len(run_test.tests_failed), " tests failed"
  if len(run_test.tests_failed) > 0:
    for test in run_test.tests_failed:
      print test
  sys.exit(len(run_test.tests_failed))

if __name__ == "__main__":
  parser = run_test.get_test_parser("usage: %prog [options] <bootstrap_test_dir>")
  (opts, args) = parser.parse_args()

  if len(args) == 0:
    print "Missing <bootstrap_test_dir>!"
    parser.print_help()
    sys.exit(1)

  run_test.options = opts
  bootstrap_dir = args[0]

  tmpdir = os.path.join(opts.bindir, 'test-tmpdir')
  run_test.ensure_dir_exists(tmpdir)

  main(bootstrap_dir, run_test.get_paths(opts, tmpdir), tmpdir)
