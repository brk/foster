from __future__ import with_statement
import time
import os
import re
import os.path
import subprocess
import sys
import shutil
import traceback

from list_all import collect_all_tests
from run_test import *

def run_all_tests(bootstrap_dir, paths, tmpdir):
  tests = collect_all_tests(bootstrap_dir)
  for testpath in tests:
    
    test_tmpdir = os.path.join(tmpdir, testname(testpath))
    ensure_dir_exists(test_tmpdir)
    try:
      run_one_test(testpath, paths, test_tmpdir)
    except KeyboardInterrupt:
      return
    except TestFailed:
      tests_failed.add(testpath)

def main(bootstrap_dir, paths, tmpdir):
  walkstart = walltime()
  run_all_tests(bootstrap_dir, paths, tmpdir)
  walkend = walltime()
  print "Total time: %d ms" % elapsed(walkstart, walkend)

  print len(tests_passed), " tests passed"

  print len(tests_failed), " tests failed"
  if len(tests_failed) > 0:
    for test in tests_failed:
      print test
  sys.exit(len(tests_failed))

if __name__ == "__main__":
  parser = get_test_parser("usage: %prog [options] <bootstrap_test_dir>")
  (options, args) = parser.parse_args()

  if len(args) == 0:
    print "Missing <bootstrap_test_dir>!"
    parser.print_help()
    sys.exit(1)

  bootstrap_dir = args[0]
  bindir = options.bindir

  tmpdir = os.path.join(bindir, 'test-tmpdir')
  ensure_dir_exists(tmpdir)


  print options
  print args

  main(bootstrap_dir, get_paths(bindir, options), tmpdir)
