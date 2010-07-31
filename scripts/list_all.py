from __future__ import with_statement
import os
import os.path
import sys

from parse_args import parse_args

def collect_all_tests(bootstrap_dir):
  rv = []
  for root, dirs, files in os.walk(bootstrap_dir, topdown=False):
    base = os.path.basename(root)

    code_path = os.path.join(root, base + ".foster")
    have_code = os.path.exists(code_path)

    if have_code:
      rv.append(code_path)
  return rv

def _main(bootstrap_dir):
  testpaths = collect_all_tests(bootstrap_dir)
  for testpath in testpaths:
    print testpath

if __name__ == "__main__":
  for var,val in parse_args("bootstrap_path").items():
    exec "%s = '%s'" % (var, val)
  bootstrap_dir = os.path.abspath(bootstrap_path)
  _main(bootstrap_dir)
