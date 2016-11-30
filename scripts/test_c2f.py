#!/usr/bin/env python2

from __future__ import with_statement

import os.path
import subprocess
import fnmatch
import hashlib
import shutil

csmith_dir = os.path.expanduser("~/sw/local/csmith-2016-08-26")
csmith_inc = os.path.join(csmith_dir, 'include', 'csmith-2.3.0')

# returns status
def run_cmd(cmd, stdout=None, stderr=None, stdin=None):
  if type(cmd) == str:
    cmd = cmd.strip().split(' ')

  rv = 1
  try:
    #print ' '.join(cmd)
    rv = subprocess.call(cmd, stdout=stdout, stderr=stderr, stdin=stdin)
  except OSError:
    print ": error: Unable to execute ", cmd
    raise
  return rv

#############################

def files_differ(a, b):
  "Returns True if diff finds a difference between file a and file b."
  with open(os.devnull, 'w') as devnull:
    rv = run_cmd(['diff', '--brief', a, b], stdout=devnull)
    if rv == 0:
        return False
    else:
        return True

def fail_reason(foster_compile_rv):
  if foster_compile_rv == 0:
    return "wrong output"
  else:
    return "couldn't compile"

def attempt_test_named(filename, copy_here_if_ok=None):
    print "Attempting test", filename

    c_code = filename
    assert c_code[-2:] == ".c"
    x = c_code[:-2] # strip the ".c" from the filename

    f_code  = "%s.foster" % x
    c_warn  = "%s.clang.warn.txt" % x
    cf_warn = "%s.c2f.warn.txt" % x
    c_out   = "%s.clang.out.txt" % x
    f_out   = "%s.foster.out.txt" % x

    c_rv = run_cmd("runclang %s -I %s" % (c_code, csmith_inc), stdout=open(c_out, 'w'), stderr=open(c_warn, 'w'))

    if c_rv == 0:
      linecount = len(open(c_code, 'r').readlines())
      print "Compiling", c_code, "to Foster... (%d lines)" % linecount
      run_cmd("c2foster %s -I %s" % (c_code, csmith_inc), stdout=open(f_code, 'w'), stderr=open(cf_warn, 'w'))

      print "Compiling and running the generated Foster code..."
      f_c_rv = run_cmd("runfoster %s" % f_code, stdout=open(f_out, 'w'))


      linecount = len(open(c_out, 'r').readlines())
      print "Diffing... (%d lines)" % linecount

      if files_differ(c_out, f_out):
          print "Test case", c_code, "            FAILED (%s)" % fail_reason(f_c_rv)
      else:
          print "Test case", c_code, "passed"
          if copy_here_if_ok is not None:
            filename = hashlib.md5(open(c_code, 'r').read()).hexdigest() + ".c"
            shutil.copyfile(c_code, os.path.join(copy_here_if_ok, filename))
    else:
          print "Test case", c_code, "skipped because the C code exited under murky circumstances."

    print "--------------------------------------------------"

def run_on_test_c2f():
  for root, d, files in os.walk("../test/c2f"):
    for cfile in fnmatch.filter(files, "*.c"):
      if not 'csmith' in root:
        attempt_test_named(os.path.join(root, cfile))

def run_on_csf_files():
  for root, d, files in os.walk("."):
    for cfile in fnmatch.filter(files, "csf_*.c"):
      attempt_test_named(os.path.join(root, cfile))

if __name__ == '__main__':
  #run_on_test_c2f()
  run_on_csf_files()
