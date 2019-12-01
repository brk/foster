#!/usr/bin/env python2

from __future__ import with_statement
import os
import os.path
import sys

from inspect import getsourcefile

from optparse import OptionParser

def collect_all_tests_ext(bootstrap_dir, f):
  rv = []
  for root, dirs, files in os.walk(bootstrap_dir, topdown=False):
    base = os.path.basename(root)

    code_path = os.path.join(root, base + ".foster")
    have_code = os.path.exists(code_path)

    if have_code:
      rv.append((f(code_path), code_path))
  return rv

def path_nil_info(path):
  return []

def path_lines_info(path):
  numlines = sum(1 for line in open(path))
  return [numlines]

def info_lines(info): return info[0]

def collect_all_tests(bootstrap_dir):
  return [t for (i, t) in collect_all_tests_ext(bootstrap_dir, path_nil_info)]

def _main(bootstrap_dir):
  if options.lines:
    f = path_lines_info
  else:
    f = path_nil_info

  testpaths = collect_all_tests_ext(bootstrap_dir, f)

  for (info, testpath) in testpaths:
    if options.lines:
      print info_lines(info), testpath
    else:
      print testpath

def get_list_all_parser():
  parser = OptionParser()
  parser.add_option("--lines", action="store_true", dest="lines", default=False,
                    help="Output # of lines for each file found. Consider piping to `sort -h[r]`")
  parser.add_option("--testdir", action="store", dest="testdir", default=None,
                    help="Directory to search for tests (default: ROOT/test")
  return parser

if __name__ == "__main__":
  parser = get_list_all_parser()
  (options, args) = parser.parse_args()

  if options.testdir is not None:
    bootstrap_path = os.path.abspath(options.testdir)
  else:
    bootstrap_path = os.path.join(getsourcefile(lambda:0), '..', '..', 'test')

  _main(os.path.abspath(bootstrap_path))
